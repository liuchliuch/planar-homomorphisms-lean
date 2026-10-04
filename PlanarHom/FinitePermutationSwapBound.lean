import PlanarHom.PermutationGraphCycleCount
import PlanarHom.OccurrenceEdgeAdditionComponents
import PlanarHom.FinitePermutationCut

/-! The cycle-count bounds needed for hereditary planar Euler. The proof uses
actual graph components and a unique-exit cut, including fixed-point cycles. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
open MultiGraph
variable {D : Type} [Fintype D]

def swapInput (P : Equiv.Perm D) (a b : D) : Equiv.Perm D := (Equiv.swap a b).trans P

@[simp] theorem swapInput_a (P : Equiv.Perm D) (a b : D) : swapInput P a b a=P b := by simp [swapInput]
@[simp] theorem swapInput_b (P : Equiv.Perm D) (a b : D) : swapInput P a b b=P a := by simp [swapInput]
@[simp] theorem swapInput_twice (P : Equiv.Perm D) (a b : D) : swapInput (swapInput P a b) a b=P := by
  ext x
  simp [swapInput]

theorem augmented_swap_step (P : Equiv.Perm D) (a b x : D) :
    ((permutationGraph P).withEdge a b).componentSetoid Finset.univ x (swapInput P a b x) := by
  have hs : ((permutationGraph P).withEdge a b).componentSetoid Finset.univ x (Equiv.swap a b x) := by
    by_cases ha : x=a
    · subst x
      simpa using (show ((permutationGraph P).withEdge a b).componentSetoid Finset.univ a b from
        Relation.EqvGen.rel _ _ ⟨.inr (),Finset.mem_univ _,rfl,rfl⟩)
    · by_cases hb : x=b
      · subst x
        simpa using (Relation.EqvGen.symm _ _
          (show ((permutationGraph P).withEdge a b).componentSetoid Finset.univ a b from
            Relation.EqvGen.rel _ _ ⟨.inr (),Finset.mem_univ _,rfl,rfl⟩))
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  exact Relation.EqvGen.trans _ _ _ hs
    (Relation.EqvGen.rel _ _ ⟨.inl (Equiv.swap a b x),Finset.mem_univ _,rfl,rfl⟩)

theorem augmented_swap_reach (P : Equiv.Perm D) (a b : D) {x y : D}
    (h : ((permutationGraph (swapInput P a b)).withEdge a b).componentSetoid Finset.univ x y) :
    ((permutationGraph P).withEdge a b).componentSetoid Finset.univ x y := by
  induction h with
  | rel x y h =>
    obtain ⟨e,_,rfl,rfl⟩ := h
    cases e with
    | inl x => exact augmented_swap_step P a b x
    | inr u => exact Relation.EqvGen.rel _ _ ⟨.inr u,Finset.mem_univ _,rfl,rfl⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

theorem augmented_swap_iff (P : Equiv.Perm D) (a b x y : D) :
    ((permutationGraph (swapInput P a b)).withEdge a b).componentSetoid Finset.univ x y ↔
    ((permutationGraph P).withEdge a b).componentSetoid Finset.univ x y := by
  constructor
  · exact augmented_swap_reach P a b
  · intro h
    have hh := augmented_swap_reach (swapInput P a b) a b (x:=x) (y:=y)
    rw [swapInput_twice] at hh
    exact hh h

theorem augmented_swap_count (P : Equiv.Perm D) (a b : D) :
    ((permutationGraph (swapInput P a b)).withEdge a b).componentCount Finset.univ=
      ((permutationGraph P).withEdge a b).componentCount Finset.univ :=
  Fintype.card_congr (Quotient.congr (Equiv.refl D) (augmented_swap_iff P a b))

theorem sameCycle_swap_of_separate (P : Equiv.Perm D) (a b : D) (h : ¬P.SameCycle a b) :
    (swapInput P a b).SameCycle a b := by
  have hab : a≠b := by intro he; subst b; exact h .rfl
  have hx := FinitePermutationCut.sameCycle_of_unique_exit (swapInput P a b)
    (P.SameCycle a) b a (by rw [swapInput_b]; exact Equiv.Perm.SameCycle.rfl.apply_right) h (by
      intro x hin hout
      by_contra hxa
      have hxb : x≠b := by intro he; subst x; exact h hin
      apply hout
      simpa [swapInput,Equiv.swap_apply_of_ne_of_ne hxa hxb] using hin.apply_right)
  exact hx.symm

/-- Swapping arrows at different cycles merges exactly those two cycles. -/
theorem count_swap_of_separate (P : Equiv.Perm D) (a b : D) (h : ¬P.SameCycle a b) :
    count (swapInput P a b)+1=count P := by
  have hp := (permutationGraph P).withEdge_count_of_not_related a b
    (fun hh => h ((permutation_reach_iff P a b).mp hh))
  have hq := (permutationGraph (swapInput P a b)).withEdge_count_of_related a b
    ((permutation_reach_iff _ a b).mpr (sameCycle_swap_of_separate P a b h))
  rw [← augmented_swap_count P a b,hq] at hp
  simpa only [permutation_componentCount] using hp

/-- An arbitrary transposition increases the number of cycles by at most one. -/
theorem count_swap_le_add_one (P : Equiv.Perm D) (a b : D) :
    count (swapInput P a b)≤count P+1 := by
  by_cases h : P.SameCycle a b
  · have hp := (permutationGraph P).withEdge_count_of_related a b ((permutation_reach_iff P a b).mpr h)
    have hq := (permutationGraph (swapInput P a b)).componentCount_le_withEdge_add_one a b
    rw [augmented_swap_count,hp] at hq
    simpa only [permutation_componentCount] using hq
  · have hh := count_swap_of_separate P a b h
    omega
end PlanarHom.FinitePermutationCycles
