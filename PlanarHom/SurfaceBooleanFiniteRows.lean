import PlanarHom.SurfaceBooleanCoordinates
import PlanarHom.SurfaceBooleanCoordinateMachines
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! NEW finite-width interpretation. Width is a materialized Boolean header,
so every generated coordinate is charged to the actual input encoding. -/
namespace PlanarHom.SurfaceBooleanRows
open scoped BigOperators

def normalize (shape r : Row) : Row := shape.zipIdx.map (fun p => bitAt r p.2)
def unit (shape : Row) (j : ℕ) : Row := shape.zipIdx.map (fun p => decide (p.2=j))
def transpose (shape : Row) (rs : List Row) : List Row :=
  shape.zipIdx.map (fun p => rs.map (fun r => bitAt r p.2))
def normalizedRows (shape : Row) (rs : List Row) : List Row := rs.map (normalize shape)
def kernelRows (shape : Row) (rs : List Row) : List Row :=
  let bs := basis (normalizedRows shape rs)
  transpose shape (shape.zipIdx.map (fun p => reduce bs (unit shape p.2)))

def finiteValue (m : ℕ) (r : Row) : Fin m→ZMod 2 := fun i => value r i.val

def unitVector {m : ℕ} (j : Fin m) : Vector := fun i => if i=j.val then 1 else 0

def Bounded (m : ℕ) (x : Vector) : Prop := ∀ i, m ≤ i → x i = 0

theorem value_bounded (m : ℕ) (r : Row) (hr : r.length≤m) : Bounded m (value r) := by
  intro i hi
  simp [value,bitAt,List.getElem?_eq_none (by omega : r.length ≤ i)]

@[simp] theorem normalize_length (shape r : Row) : (normalize shape r).length=shape.length := by
  simp [normalize]
@[simp] theorem unit_length (shape : Row) (j : ℕ) : (unit shape j).length=shape.length := by
  simp [unit]

theorem normalize_bitAt (shape r : Row) (i : ℕ) (hi : i<shape.length) :
    bitAt (normalize shape r) i=bitAt r i := by
  simp [normalize,bitAt,List.getElem?_eq_getElem hi,List.getElem?_map,List.getElem?_zipIdx,hi]

theorem normalize_finiteValue (shape r : Row) :
    finiteValue shape.length (normalize shape r)=finiteValue shape.length r := by
  funext i
  exact congrArg bitValue (normalize_bitAt shape r i.val i.isLt)

theorem unit_value (shape : Row) (j : Fin shape.length) : value (unit shape j.val)=unitVector j := by
  funext i
  by_cases hi : i<shape.length
  · simp [unit,value,bitAt,unitVector,List.getElem?_map,List.getElem?_zipIdx,
      List.getElem?_eq_getElem hi,hi,bitValue]
  · have hz := value_bounded shape.length (unit shape j.val) (by simp) i (Nat.le_of_not_gt hi)
    rw [hz]
    simp [unitVector,show i≠j.val by omega]

theorem unitVector_bounded {m : ℕ} (j : Fin m) : Bounded m (unitVector j) := by
  intro i hi
  simp [unitVector,show i≠j.val by omega]

theorem sum_units {m : ℕ} (x : Vector) (hx : Bounded m x) :
    (∑j:Fin m,x j.val • unitVector j)=x := by
  funext i
  by_cases hi : i<m
  · have he : ∀ j : Fin m, (i=j.val) ↔ (⟨i,hi⟩:Fin m)=j := fun j => (Fin.ext_iff : ((⟨i,hi⟩:Fin m)=j ↔ i=j.val)).symm
    simp [unitVector,Finset.sum_apply,he]
  · have hn : ∀j:Fin m,i≠j.val := fun j => by omega
    simp [unitVector,hn,hx i (Nat.le_of_not_gt hi)]

def pair (m : ℕ) (x : Fin m→ZMod 2) : Vector→ₗ[ZMod 2] ZMod 2 :=
  ∑i:Fin m,(x i) • LinearMap.proj i.val

@[simp] theorem pair_apply (m : ℕ) (x : Fin m→ZMod 2) (y : Vector) :
    pair m x y=∑i,x i*y i.val := by simp [pair]

@[simp] theorem pair_unit {m : ℕ} (x : Fin m→ZMod 2) (j : Fin m) : pair m x (unitVector j)=x j := by
  simp [pair_apply,unitVector,Fin.val_inj]

end PlanarHom.SurfaceBooleanRows
