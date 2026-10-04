import PlanarHom.RotationRowConcatenation
import PlanarHom.RotationDartRelabel

/-! NEW literal cyclic row cut at a specified closing dart. The selected
rotation preserves every original successor. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {D : Type} [Fintype D] [dD : DecidableEq D]

 omit dD in
 theorem swapInput_apply_of_ne (P : Equiv.Perm D) (a b z : D) (ha : z≠a) (hb : z≠b) :
    swapInput P a b z=P z := by
  simp only [swapInput,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne ha hb]

structure EndingRow (xs : List D) (a : D) where
  before : List D
  nodup : (before++[a]).Nodup
  mem : ∀b,b∈before++[a] ↔ b∈xs
  permutation : (before++[a]).formPerm=xs.formPerm

 theorem exists_endingRow (xs : List D) (a : D) (hn : xs.Nodup) (ha : a∈xs) : Nonempty (EndingRow xs a) := by
  obtain ⟨pre,post,h⟩:=List.append_of_mem ha
  have hr : xs.rotate (pre++[a]).length=(post++pre)++[a] := by
    rw [h]
    have hh:=List.rotate_append_length_eq (pre++[a]) post
    simpa only [List.append_assoc,List.singleton_append] using hh
  refine ⟨⟨post++pre,?_,?_,?_⟩⟩
  · rw [←hr]
    exact List.nodup_rotate.mpr hn
  · intro b
    rw [←hr,List.mem_rotate]
  · rw [←hr,List.formPerm_rotate xs hn]

 def endingRow (xs : List D) (a : D) (hn : xs.Nodup) (ha : a∈xs) : EndingRow xs a :=
  Classical.choice (exists_endingRow xs a hn ha)

 theorem formPerm_append_endings (xs ys : List D) (a b : D) (ha : a∉ys++[b]) :
    (xs++[a]++ys++[b]).formPerm=
      swapInput ((xs++[a]).formPerm*(ys++[b]).formPerm) a b := by
  have he : dD=Classical.decEq D := Subsingleton.elim _ _
  subst dD
  cases ys with
  | nil => simpa [List.append_assoc] using
      formPerm_concat_closing xs a b [] ha
  | cons c ys =>
      have hh:=formPerm_concat_closing xs a c (ys++[b]) (by simpa using ha)
      simpa [List.append_assoc] using hh

end PlanarHom.FinitePermutationCycles
