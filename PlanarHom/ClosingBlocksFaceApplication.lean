import PlanarHom.RotationRowEnding

/-! The local row law used to identify an assembled graph with the disjoint
face-swap program. It applies to literal lifted blocks on one global carrier. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {D : Type} [Fintype D] [dD : DecidableEq D]

 theorem closingBlocks_apply (R : Equiv.Perm D) (xs ys : List D) (a b z : D)
    (hd : List.Disjoint (xs++[a]) (ys++[b]))
    (hl : ∀u∈xs++[a],R u=(xs++[a]).formPerm u)
    (hr : ∀u∈ys++[b],R u=(ys++[b]).formPerm u)
    (hz : z∈(xs++[a])++(ys++[b])) :
    ((xs++[a])++(ys++[b])).formPerm z=swapInput R a b z := by
  have hdec : dD=Classical.decEq D := Subsingleton.elim _ _
  subst dD
  have ha : a∉ys++[b] := fun h => hd (by simp) h
  have hbase : ∀u∈(xs++[a])++(ys++[b]),
      ((xs++[a]).formPerm*(ys++[b]).formPerm) u=R u := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · have hnot : u∉ys++[b] := fun hh => hd hu hh
      rw [Equiv.Perm.mul_apply,List.formPerm_apply_of_notMem hnot]
      exact (hl u hu).symm
    · have hm := List.formPerm_apply_mem_of_mem hu
      have hnot : (ys++[b]).formPerm u∉xs++[a] := fun hh => hd hh hm
      rw [Equiv.Perm.mul_apply,List.formPerm_apply_of_notMem hnot]
      exact (hr u hu).symm
  have hm : Equiv.swap a b z∈(xs++[a])++(ys++[b]) := by
    by_cases hza : z=a
    · subst z; simp
    · by_cases hzb : z=b
      · subst z; simp
      · simpa only [Equiv.swap_apply_of_ne_of_ne hza hzb] using hz
  have he : ((xs++[a])++(ys++[b])).formPerm=
      swapInput ((xs++[a]).formPerm*(ys++[b]).formPerm) a b := by
    simpa only [List.append_assoc] using formPerm_append_endings xs ys a b ha
  rw [he]
  exact hbase _ hm

 theorem closingBlocks_face_apply (R J : Equiv.Perm D) (xs ys : List D) (a b z : D)
    (hd : List.Disjoint (xs++[a]) (ys++[b]))
    (hl : ∀u∈xs++[a],R u=(xs++[a]).formPerm u)
    (hr : ∀u∈ys++[b],R u=(ys++[b]).formPerm u)
    (hz : J z∈(xs++[a])++(ys++[b])) :
    (((xs++[a])++(ys++[b])).formPerm*J) z=
      swapInput (R*J) (J.symm a) (J.symm b) z := by
  have h := closingBlocks_apply R xs ys a b (J z) hd hl hr hz
  change _=(swapInput R a b*J) z at h
  rw [face_of_row_swap] at h
  exact h
end PlanarHom.FinitePermutationCycles
