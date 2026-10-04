import PlanarHom.FinitePermutationSwapBound
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! Exact splitting of a literal permutation cycle by swapping two different
outgoing arrows. The invariant interval proves separation constructively. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {D : Type} [Fintype D]

 theorem not_sameCycle_swap_of_same (P : Equiv.Perm D) (a b : D) (hne : a≠b)
    (hab : P.SameCycle a b) : ¬(swapInput P a b).SameCycle a b := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts a)
  obtain ⟨z,hz⟩ := hab.exists_nat_pow_eq
  let n := z%Function.minimalPeriod P a
  have hn : n<Function.minimalPeriod P a := Nat.mod_lt _ hp
  have hnb : P^[n] a=b := by
    rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow]
    exact hz
  have hnpos : 0<n := by
    by_contra h
    have hh : n=0 := by omega
    rw [hh,Function.iterate_zero_apply] at hnb
    exact hne hnb
  let S : D → Prop := fun x => ∃j,j<n ∧ P^[j] (P a)=x
  have hna : ¬S a := by
    rintro ⟨j,hj,hja⟩
    have heq : P^[j+1] a=P^[0] a := by simpa only [Function.iterate_succ_apply,Function.iterate_zero_apply] using hja
    have hh := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (by omega : j+1<Function.minimalPeriod P a) hp).mp heq
    omega
  have hsb : S b := by
    refine ⟨n-1,by omega,?_⟩
    rw [← Function.iterate_succ_apply]
    rw [show (n-1).succ=n by omega]
    exact hnb
  have hS : ∀x,S x → S (swapInput P a b x) := by
    intro x hx
    by_cases hxb : x=b
    · subst x
      rw [swapInput_b]
      exact ⟨0,hnpos,rfl⟩
    · have hxa : x≠a := by intro h; subst x; exact hna hx
      rw [swapInput,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hxa hxb]
      obtain ⟨j,hj,hjx⟩ := hx
      have hj' : j+1<n := by
        by_contra h
        have hje : j+1=n := by omega
        apply hxb
        have heq : P^[j+1] a=x := by simpa only [Function.iterate_succ_apply] using hjx
        rw [hje,hnb] at heq
        exact heq.symm
      exact ⟨j+1,hj',by rw [Function.iterate_succ_apply',hjx]⟩
  intro h
  obtain ⟨j,hj⟩ := h.symm.exists_nat_pow_eq
  have hi : ∀j,S ((swapInput P a b)^[j] b) := by
    intro j
    induction j with
    | zero => exact hsb
    | succ j ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  have hh := hi j
  rw [Equiv.Perm.iterate_eq_pow,hj] at hh
  exact hna hh

 theorem count_swap_of_same (P : Equiv.Perm D) (a b : D) (hne : a≠b) (hab : P.SameCycle a b) :
    count (swapInput P a b)=count P+1 := by
  have h := count_swap_of_separate (swapInput P a b) a b (not_sameCycle_swap_of_same P a b hne hab)
  rw [swapInput_twice] at h
  exact h.symm
end PlanarHom.FinitePermutationCycles
