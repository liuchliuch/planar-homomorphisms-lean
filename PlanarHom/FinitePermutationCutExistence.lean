import PlanarHom.FinitePermutationCutInterval
import Mathlib.Dynamics.PeriodicPts.Lemmas

namespace PlanarHom.FinitePermutationCut

 theorem exists_cut_interval {A : Type*} [Finite A] (P : Equiv.Perm A) (q : A → Prop) (a b : A)
    (hstart : ¬q a) (henter : q (P a)) (hinside : q b) (hexit : ¬q (P b))
    (hentry_unique : ∀ x, ¬q x → q (P x) → x=a)
    (hexit_unique : ∀ x, q x → ¬q (P x) → x=b) :
    ∃ k, 0 < k ∧ k < Function.minimalPeriod P a ∧ P^[k] a=b ∧
      ∀ i, i < Function.minimalPeriod P a → (q (P^[i] a) ↔ 0 < i ∧ i≤k) := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts a)
  obtain ⟨n,hn⟩ := (sameCycle_of_unique_exit P q a b henter hstart hexit_unique).exists_nat_pow_eq
  let k := n % Function.minimalPeriod P a
  have hk : k < Function.minimalPeriod P a := Nat.mod_lt _ hp
  have hkb : P^[k] a=b := by
    rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow]
    exact hn
  have hkpos : 0 < k := by
    by_contra h
    have hz : k=0 := by omega
    rw [hz,Function.iterate_zero_apply] at hkb
    exact hstart (hkb.symm ▸ hinside)
  exact ⟨k,hkpos,hk,hkb,iterate_cut_interval P q a b hstart henter hexit hentry_unique hexit_unique k hk hkb⟩

end PlanarHom.FinitePermutationCut
