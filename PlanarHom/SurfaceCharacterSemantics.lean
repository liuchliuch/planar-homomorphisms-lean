import PlanarHom.SurfaceFKTProgram
import PlanarHom.SurfaceF2Characters

/-! NEW exact interpretation of bounded Boolean character enumeration and
its literal field-valued product. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceBooleanRows

theorem allWords_perm (n : ℕ) : (allWords n).Perm
    ((Finset.univ : Finset (Fin n→Bool)).toList.map List.ofFn) := by
  apply (List.perm_ext_iff_of_nodup (allWords_nodup n)
    ((Finset.nodup_toList (Finset.univ : Finset (Fin n→Bool))).map List.ofFn_injective)).mpr
  intro r
  rw [mem_allWords]
  simp only [List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and]
  constructor
  · intro h
    subst n
    exact ⟨r.get,List.ofFn_get r⟩
  · rintro ⟨x,rfl⟩
    simp

theorem sum_allWords {A : Type*} [AddCommMonoid A] (n : ℕ) (f : Row→A) :
    ((allWords n).map f).sum=∑x:Fin n→Bool,f (List.ofFn x) := by
  rw [((allWords_perm n).map f).sum_eq,List.map_map]
  rw [←List.sum_toFinset _ (Finset.nodup_toList (Finset.univ : Finset (Fin n→Bool)))]
  simp

theorem sum_boundedWords {A : Type*} [AddCommMonoid A] (bound n : ℕ) (h : n≤bound) (f : Row→A) :
    ((boundedWords bound n).map f).sum=∑x:Fin n→Bool,f (List.ofFn x) := by
  rw [boundedWords_eq,if_pos h]
  exact sum_allWords n f

@[simp] theorem finiteValue_ofFn {n : ℕ} (x : Fin n→Bool) :
    finiteValue n (List.ofFn x)=SurfaceBooleanGauss.ofBits x := by
  funext i
  simp [finiteValue,value,bitAt,SurfaceBooleanGauss.ofBits,bitValue,i.isLt]

end PlanarHom.SurfaceBooleanRows
namespace PlanarHom.SurfaceFKT
open SurfaceBooleanRows SurfaceBooleanGauss
variable {K : Type} [Field K] [DecidableEq K]

theorem characterValue_ofFn {n : ℕ} (u : Bits n) (x : Row) :
    characterValue (K:=K) (List.ofFn u) x=characterF2 u (finiteValue n x) := by
  have he : ((List.ofFn u).zipIdx.map (fun p => if p.1 && bitAt x p.2 then (-1:K) else 1))=
      List.ofFn (fun i:Fin n => if u i && bitAt x i.val then (-1:K) else 1) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [characterValue,he,List.prod_ofFn]
  unfold characterF2 character toBits
  apply Finset.prod_congr rfl
  intro i _
  cases hu : u i <;> cases hx : bitAt x i.val <;>
    simp [bitSign,finiteValue,SurfaceBooleanRows.value,bitValue,hu,hx]

theorem characterValue_ofFn_ofFn {n : ℕ} (u x : Bits n) :
    characterValue (K:=K) (List.ofFn u) (List.ofFn x)=character u x := by
  rw [characterValue_ofFn,finiteValue_ofFn]
  simp [characterF2]

end PlanarHom.SurfaceFKT
