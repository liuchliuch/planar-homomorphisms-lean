import PlanarHom.FinitePermutationCycleCount

/-! NEW cycle quotient transport from a literal permutation conjugacy. -/
namespace PlanarHom.FinitePermutationCycles
variable {A B : Type*} [Finite A] [Finite B]

theorem sameCycle_iff_of_step (P : Equiv.Perm A) (Q : Equiv.Perm B) (e : A≃B)
    (he : ∀ a, e (P a)=Q (e a)) (a b : A) : P.SameCycle a b ↔ Q.SameCycle (e a) (e b) := by
  have hi : ∀ n a, e (P^[n] a)=Q^[n] (e a) := by
    intro n a
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',he,ih,Function.iterate_succ_apply']
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),?_⟩
    rw [zpow_natCast,←Equiv.Perm.iterate_eq_pow,←hi]
    simpa only [Equiv.Perm.iterate_eq_pow,hn]
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),?_⟩
    apply e.injective
    rw [zpow_natCast,←Equiv.Perm.iterate_eq_pow,hi,Equiv.Perm.iterate_eq_pow,hn]

theorem count_of_step (P : Equiv.Perm A) (Q : Equiv.Perm B) (e : A≃B)
    (he : ∀ a, e (P a)=Q (e a)) : count P=count Q :=
  count_congr P Q e (sameCycle_iff_of_step P Q e he)

theorem count_permCongr (P : Equiv.Perm A) (e : A≃B) : count (e.permCongr P)=count P := by
  symm
  apply count_of_step P (e.permCongr P) e
  intro a
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]

/-- Compatibility name from the independently reconstructed bouquet module. -/
theorem sameCycle_semiconj (P : Equiv.Perm A) (Q : Equiv.Perm B) (e : A≃B)
    (he : ∀a,e (P a)=Q (e a)) (a b : A) :
    P.SameCycle a b ↔ Q.SameCycle (e a) (e b) :=
  sameCycle_iff_of_step P Q e he a b

/-- Compatibility name from the independently reconstructed bouquet module. -/
theorem count_semiconj (P : Equiv.Perm A) (Q : Equiv.Perm B) (e : A≃B)
    (he : ∀a,e (P a)=Q (e a)) : count P=count Q := count_of_step P Q e he

end PlanarHom.FinitePermutationCycles
