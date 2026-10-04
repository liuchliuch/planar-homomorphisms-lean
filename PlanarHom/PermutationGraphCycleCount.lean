import PlanarHom.PermutationGraphComponents
import PlanarHom.FinitePermutationCycleCount

noncomputable section
namespace PlanarHom.MultiGraph
variable {D : Type} [Fintype D]

theorem permutation_reach_iff (P : Equiv.Perm D) (u v : D) :
    (permutationGraph P).componentSetoid Finset.univ u v ↔ P.SameCycle u v := by
  constructor
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨d,_,rfl,rfl⟩ := h
      exact Equiv.Perm.SameCycle.rfl.apply_right
    | refl => exact .rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ij => exact ih.trans ij
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hi : ∀n,(permutationGraph P).componentSetoid Finset.univ u (P^[n] u) := by
      intro n
      induction n with
      | zero => exact Relation.EqvGen.refl _
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ ⟨P^[n] u,Finset.mem_univ _,rfl,rfl⟩)
    simpa only [Equiv.Perm.iterate_eq_pow,hn] using hi n

def permutationCycleEquiv (P : Equiv.Perm D) :
    (permutationGraph P).Components Finset.univ ≃ Quotient (Equiv.Perm.SameCycle.setoid P) :=
  Quotient.congr (Equiv.refl D) (permutation_reach_iff P)

theorem permutation_componentCount (P : Equiv.Perm D) :
    (permutationGraph P).componentCount Finset.univ=FinitePermutationCycles.count P := by
  rw [componentCount,← Nat.card_eq_fintype_card]
  exact Nat.card_congr (permutationCycleEquiv P)
end PlanarHom.MultiGraph
