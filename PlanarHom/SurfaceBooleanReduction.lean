import PlanarHom.SurfaceBooleanEchelon
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! NEW exact linear interpretation and kernel of the executable row reducer. -/
namespace PlanarHom.SurfaceBooleanRows
open scoped CharTwo
abbrev Vector := ℕ → ZMod 2

def clearMap (p : PivotRow) : Vector →ₗ[ZMod 2] Vector where
  toFun x := x + (x p.1) • value p.2
  map_add' x y := by ext i; simp [add_smul]; ring
  map_smul' c x := by ext i; simp [smul_add,smul_smul]; ring

@[simp] theorem clearMap_apply (p : PivotRow) (x : Vector) :
    clearMap p x=x+(x p.1)•value p.2 := rfl

theorem value_clear (r : Row) (p : PivotRow) : value (clear r p)=clearMap p (value r) := by
  cases h : bitAt r p.1 <;> simp [clear,h,clearMap_apply,value_xorRows,value,bitValue,h]

def reduceMap : BasisRows → (Vector →ₗ[ZMod 2] Vector)
  | [] => LinearMap.id
  | p::bs => (reduceMap bs).comp (clearMap p)

@[simp] theorem reduceMap_nil (x : Vector) : reduceMap [] x=x := rfl
@[simp] theorem reduceMap_cons (p : PivotRow) (bs : BasisRows) (x : Vector) :
    reduceMap (p::bs) x=reduceMap bs (clearMap p x) := rfl

theorem value_reduce (bs : BasisRows) (r : Row) : value (reduce bs r)=reduceMap bs (value r) := by
  induction bs generalizing r with
  | nil => rfl
  | cons p bs ih =>
      change value (reduce bs (clear r p))=reduceMap bs (clearMap p (value r))
      rw [ih,value_clear]

def rowSpan (bs : BasisRows) : Submodule (ZMod 2) Vector :=
  Submodule.span (ZMod 2) {x | ∃p∈bs,value p.2=x}

theorem row_mem_span (bs : BasisRows) (p : PivotRow) (hp : p∈bs) : value p.2∈rowSpan bs :=
  Submodule.subset_span ⟨p,hp,rfl⟩

theorem rowSpan_mono {bs cs : BasisRows} (h : bs.Sublist cs) : rowSpan bs≤rowSpan cs := by
  apply Submodule.span_mono
  rintro x ⟨p,hp,rfl⟩
  exact ⟨p,h.subset hp,rfl⟩

theorem reduceMap_row_zero (bs : BasisRows) (h : Echelon bs) :
    ∀p∈bs,reduceMap bs (value p.2)=0 := by
  induction bs with
  | nil => simp
  | cons p bs ih =>
      have hp : bitAt p.2 p.1=true := h.1 p (by simp)
      have ht : Echelon bs := ⟨fun q hq => h.1 q (by simp [hq]),h.2.tail⟩
      intro q hq
      rcases List.mem_cons.mp hq with hqp | hq
      · subst q
        rw [reduceMap_cons]
        have hz : clearMap p (value p.2)=0 := by
          rw [clearMap_apply]
          have hval : value p.2 p.1=1 := by simp [value,hp]
          rw [hval,one_smul]
          ext i
          simp
        rw [hz,map_zero]
      · rw [reduceMap_cons]
        have hz := (List.pairwise_cons.mp h.2).1 q hq
        have hc : clearMap p (value q.2)=value q.2 := by simp [clearMap_apply,value,hz]
        rw [hc]
        exact ih ht q hq

theorem rowSpan_le_ker (bs : BasisRows) (h : Echelon bs) : rowSpan bs≤LinearMap.ker (reduceMap bs) := by
  apply Submodule.span_le.mpr
  rintro x ⟨p,hp,rfl⟩
  exact reduceMap_row_zero bs h p hp

theorem reduction_difference_mem (bs : BasisRows) (x : Vector) : x-reduceMap bs x∈rowSpan bs := by
  induction bs generalizing x with
  | nil => simp [rowSpan]
  | cons p bs ih =>
      have hp : value p.2∈rowSpan (p::bs) := row_mem_span _ _ (by simp)
      have hs : rowSpan bs≤rowSpan (p::bs) := rowSpan_mono (List.sublist_cons_self p bs)
      have hc : x-clearMap p x∈rowSpan (p::bs) := by
        have he : x-clearMap p x=-(x p.1)•value p.2 := by ext i; simp
        rw [he]
        exact Submodule.smul_mem _ _ hp
      have ht := hs (ih (clearMap p x))
      have he : x-reduceMap (p::bs) x =
          (x-clearMap p x)+(clearMap p x-reduceMap bs (clearMap p x)) := by
        rw [reduceMap_cons]
        abel
      rw [he]
      exact Submodule.add_mem (rowSpan (p::bs)) hc ht

theorem ker_reduceMap (bs : BasisRows) (h : Echelon bs) :
    LinearMap.ker (reduceMap bs)=rowSpan bs := by
  apply le_antisymm
  · intro x hx
    have hd := reduction_difference_mem bs x
    simpa only [LinearMap.mem_ker.mp hx,sub_zero] using hd
  · exact rowSpan_le_ker bs h

end PlanarHom.SurfaceBooleanRows
