import PlanarHom.FinitePermutationCycleCount

/-! NEW exact cycle-preserving insertion of a fresh named dart into one arrow.
The result includes singleton cycles and never introduces a virtual face. -/
noncomputable section
namespace PlanarHom.FinitePermutationCycles
variable {A : Type*} [DecidableEq A]

def insertAfter (P : Equiv.Perm A) (a : A) : Equiv.Perm (A ⊕ Unit) :=
  (Equiv.swap (.inl a) (.inr ())).trans (Equiv.sumCongr P (Equiv.refl Unit))

def collapseInserted (a : A) : A ⊕ Unit → A
  | .inl x => x
  | .inr _ => a

@[simp] theorem insertAfter_mark (P : Equiv.Perm A) (a : A) : insertAfter P a (.inl a)=.inr () := by
  simp [insertAfter]
@[simp] theorem insertAfter_new (P : Equiv.Perm A) (a : A) : insertAfter P a (.inr ())=.inl (P a) := by
  simp [insertAfter]
 theorem insertAfter_old (P : Equiv.Perm A) (a x : A) (hx : x≠a) :
    insertAfter P a (.inl x)=.inl (P x) := by
  simp [insertAfter,Equiv.swap_apply_of_ne_of_ne,hx]

 theorem inserted_step_lifts (P : Equiv.Perm A) (a x : A) :
    (insertAfter P a).SameCycle (.inl x) (.inl (P x)) := by
  by_cases hx : x=a
  · subst x
    have h : (insertAfter P a).SameCycle (.inl a)
        (insertAfter P a (insertAfter P a (.inl a))) :=
      (Equiv.Perm.SameCycle.rfl.apply_right).apply_right
    simpa only [insertAfter_mark,insertAfter_new] using h
  · have h : (insertAfter P a).SameCycle (.inl x) (insertAfter P a (.inl x)) :=
      Equiv.Perm.SameCycle.rfl.apply_right
    simpa only [insertAfter_old P a x hx] using h

 theorem collapsed_step (P : Equiv.Perm A) (a : A) (x : A ⊕ Unit) :
    P.SameCycle (collapseInserted a x) (collapseInserted a (insertAfter P a x)) := by
  cases x with
  | inl x =>
      by_cases hx : x=a
      · subst x
        rw [insertAfter_mark]
        exact .rfl
      · rw [insertAfter_old P a x hx]
        exact Equiv.Perm.SameCycle.rfl.apply_right
  | inr u =>
      cases u
      rw [insertAfter_new]
      exact Equiv.Perm.SameCycle.rfl.apply_right

 theorem sameCycle_inserted_of_old [Finite A] (P : Equiv.Perm A) (a : A) {x y : A}
    (h : P.SameCycle x y) : (insertAfter P a).SameCycle (.inl x) (.inl y) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hall : ∀ n, (insertAfter P a).SameCycle (.inl x) (.inl (P^[n] x)) := by
    intro n
    induction n with
    | zero => exact .rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (inserted_step_lifts P a _)
  have hh := hall n
  simpa only [Equiv.Perm.iterate_eq_pow,hn] using hh

 theorem sameCycle_collapsed [Finite A] (P : Equiv.Perm A) (a : A) {x y : A ⊕ Unit}
    (h : (insertAfter P a).SameCycle x y) : P.SameCycle (collapseInserted a x) (collapseInserted a y) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hall : ∀ n, P.SameCycle (collapseInserted a x) (collapseInserted a ((insertAfter P a)^[n] x)) := by
    intro n
    induction n with
    | zero => exact .rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (collapsed_step P a _)
  have hh := hall n
  simpa only [Equiv.Perm.iterate_eq_pow,hn] using hh

 theorem sameCycle_insertAfter_iff [Finite A] (P : Equiv.Perm A) (a : A) (x y : A ⊕ Unit) :
    (insertAfter P a).SameCycle x y ↔ P.SameCycle (collapseInserted a x) (collapseInserted a y) := by
  constructor
  · exact sameCycle_collapsed P a
  · intro h
    have hx : (insertAfter P a).SameCycle x (.inl (collapseInserted a x)) := by
      cases x with
      | inl x => exact .rfl
      | inr u =>
          cases u
          have hh : (insertAfter P a).SameCycle (.inl a) (insertAfter P a (.inl a)) :=
            Equiv.Perm.SameCycle.rfl.apply_right
          simpa only [insertAfter_mark,collapseInserted] using hh.symm
    have hy : (insertAfter P a).SameCycle (.inl (collapseInserted a y)) y := by
      cases y with
      | inl y => exact .rfl
      | inr u =>
          cases u
          have hh : (insertAfter P a).SameCycle (.inl a) (insertAfter P a (.inl a)) :=
            Equiv.Perm.SameCycle.rfl.apply_right
          simpa only [insertAfter_mark,collapseInserted] using hh
    exact hx.trans ((sameCycle_inserted_of_old P a h).trans hy)

def insertedCycleEquiv [Finite A] (P : Equiv.Perm A) (a : A) :
    Quotient (Equiv.Perm.SameCycle.setoid (insertAfter P a)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid P) where
  toFun := Quotient.map (collapseInserted a) (fun _ _ h => sameCycle_collapsed P a h)
  invFun := Quotient.map Sum.inl (fun _ _ h => sameCycle_inserted_of_old P a h)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    apply (sameCycle_insertAfter_iff P a _ _).mpr
    exact .rfl
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    rfl

/-- Adding a fresh dart along an existing permutation arrow preserves every
literal cycle, including an original fixed-point cycle. -/
theorem count_insertAfter [Finite A] (P : Equiv.Perm A) (a : A) : count (insertAfter P a)=count P :=
  Nat.card_congr (insertedCycleEquiv P a)

end PlanarHom.FinitePermutationCycles
