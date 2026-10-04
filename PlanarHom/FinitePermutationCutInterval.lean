import PlanarHom.FinitePermutationCut
import Mathlib.Dynamics.PeriodicPts.Defs

/-! NEW exact cyclic interval of a cut with one entering and one exiting dart. -/
namespace PlanarHom.FinitePermutationCut

/-- In one period starting at the unique entry transition, the cut occupies
precisely indices 1 through the exit index. -/
theorem iterate_cut_interval {A : Type*} (P : Equiv.Perm A) (q : A → Prop) (a b : A)
    (hstart : ¬q a) (henter : q (P a)) (hexit : ¬q (P b))
    (hentry_unique : ∀ x, ¬q x → q (P x) → x=a)
    (hexit_unique : ∀ x, q x → ¬q (P x) → x=b)
    (k : ℕ) (hk : k  <  Function.minimalPeriod P a) (hbk : P^[k] a=b)
    (i : ℕ) (hi : i  <  Function.minimalPeriod P a) :
    q (P^[i] a) ↔ 0 < i ∧ i≤k := by
  classical
  have hbefore : ∀ i, 0 < i → i≤k → q (P^[i] a) := by
    intro i hip hik
    by_contra hn
    have hout : ¬q (P^[i-1] (P a)) := by
      have he : P^[i-1] (P a)=P^[i] a := by rw [← Function.iterate_succ_apply]; congr 1; omega
      rwa [he]
    obtain ⟨j,hj,hj₁,hj₂⟩ := iterate_crosses_cut P q (P a) (i-1) henter hout
    have he : P^[j+1] a=P^[k] a := by
      rw [Function.iterate_succ_apply,hbk]
      exact hexit_unique _ hj₁ hj₂
    have hless : j+1  <  Function.minimalPeriod P a := by omega
    have heq := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hless hk).mp he
    omega
  have hafter : ∀ i, k < i → i < Function.minimalPeriod P a → ¬q (P^[i] a) := by
    intro i hki hip hqi
    have hno : ¬q (P^[k+1] a) := by simpa only [Function.iterate_succ_apply',hbk] using hexit
    have hyes : q (P^[i-(k+1)] (P^[k+1] a)) := by
      have he : P^[i-(k+1)] (P^[k+1] a)=P^[i] a := by
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      rwa [he]
    obtain ⟨j,hj,hj₁,hj₂⟩ := iterate_crosses_cut P (fun x => ¬q x) (P^[k+1] a) (i-(k+1)) hno (by simpa using hyes)
    have hentry := hentry_unique _ hj₁ (Classical.not_not.mp hj₂)
    have he : P^[j+(k+1)] a=P^[0] a := by
      rw [Function.iterate_add_apply]
      exact hentry
    have hless : j+(k+1) < Function.minimalPeriod P a := by omega
    have hz : 0 < Function.minimalPeriod P a := by omega
    have heq := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hless hz).mp he
    omega
  constructor
  · intro hq
    refine ⟨?_,?_⟩
    · by_contra h
      have hzero : i=0 := by omega
      subst i
      exact hstart hq
    · by_contra h
      exact hafter i (lt_of_not_ge h) hi hq
  · rintro ⟨hip,hik⟩
    exact hbefore i hip hik

end PlanarHom.FinitePermutationCut
