import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! NEW finite-permutation cut lemma. A unique exit from a cut must lie in every
cycle that enters the cut from outside. No parity or topology oracle is used. -/
namespace PlanarHom.FinitePermutationCut

 theorem iterate_crosses_cut {A : Type*} (f : A → A) (q : A → Prop) (x : A) (n : ℕ)
    (hin : q x) (hout : ¬q (f^[n] x)) :
    ∃ k, k<n ∧ q (f^[k] x) ∧ ¬q (f (f^[k] x)) := by
  classical
  induction n with
  | zero => exact False.elim (hout hin)
  | succ n ih =>
      by_cases hn : q (f^[n] x)
      · exact ⟨n,Nat.lt_succ_self _,hn,by simpa only [Function.iterate_succ_apply'] using hout⟩
      · obtain ⟨k,hk,h₁,h₂⟩ := ih hn
        exact ⟨k,Nat.lt_trans hk (Nat.lt_succ_self _),h₁,h₂⟩

 theorem sameCycle_of_unique_exit {A : Type*} [Finite A] (P : Equiv.Perm A) (q : A → Prop)
    (a b : A) (hin : q (P a)) (hout : ¬q a)
    (hunique : ∀ x, q x → ¬q (P x) → x=b) : P.SameCycle a b := by
  have hc : P.SameCycle (P a) a := Equiv.Perm.sameCycle_apply_left.mpr .rfl
  obtain ⟨n,hn⟩ := hc.exists_nat_pow_eq
  have hexit : ¬q (P^[n] (P a)) := by simpa only [Equiv.Perm.iterate_eq_pow,hn] using hout
  obtain ⟨k,_,hk₁,hk₂⟩ := iterate_crosses_cut P q (P a) n hin hexit
  have he := hunique _ hk₁ hk₂
  have hi : P^[k+1] a=b := by rw [Function.iterate_succ_apply]; exact he
  exact ⟨(k+1:ℕ),by simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hi⟩

end PlanarHom.FinitePermutationCut
