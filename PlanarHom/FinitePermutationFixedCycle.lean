import PlanarHom.FinitePermutationCycleCount
import Mathlib.Data.Fintype.Sum

/-! NEW literal addition of one fixed-point face cycle. -/
noncomputable section
namespace PlanarHom.FinitePermutationCycles
variable {A : Type*}

def addFixed (P : Equiv.Perm A) : Equiv.Perm (A⊕Unit) := Equiv.sumCongr P (Equiv.refl Unit)

theorem addFixed_pow_inl (P : Equiv.Perm A) (x : A) (n : ℕ) :
    (addFixed P ^ n) (.inl x)=.inl ((P^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ',Equiv.Perm.mul_apply]
      rw [ih]
      rfl

theorem sameCycle_addFixed_inl [Finite A] (P : Equiv.Perm A) (x y : A) :
    (addFixed P).SameCycle (.inl x) (.inl y) ↔ P.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨n,hn⟩:=h.exists_nat_pow_eq
    rw [addFixed_pow_inl] at hn
    exact ⟨n,by simpa only [zpow_natCast] using Sum.inl.inj hn⟩
  · intro h
    obtain ⟨n,hn⟩:=h.exists_nat_pow_eq
    exact ⟨n,by simpa only [zpow_natCast,addFixed_pow_inl,hn]⟩

theorem not_sameCycle_addFixed_mixed (P : Equiv.Perm A) (x : A) (u : Unit) :
    ¬(addFixed P).SameCycle (.inl x) (.inr u) := by
  intro h
  have he:=h.eq_of_right (show addFixed P (.inr u)=.inr u from rfl)
  cases he

def fixedCycleEquiv [Finite A] (P : Equiv.Perm A) :
    Quotient (Equiv.Perm.SameCycle.setoid (addFixed P)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid P)⊕Unit where
  toFun := Quotient.lift
    (fun x=>match x with | .inl a=>.inl (Quotient.mk _ a) | .inr u=>.inr u)
    (by
      intro x y h
      cases x with
      | inl x =>
          cases y with
          | inl y => exact congrArg Sum.inl (Quotient.sound ((sameCycle_addFixed_inl P x y).mp h))
          | inr u => exact (not_sameCycle_addFixed_mixed P x u h).elim
      | inr u =>
          cases y with
          | inl y => exact (not_sameCycle_addFixed_mixed P y u h.symm).elim
          | inr v => cases u; cases v; rfl)
  invFun x := match x with
    | .inl q=>Quotient.map Sum.inl (fun {a b} h=>(sameCycle_addFixed_inl P a b).mpr h) q
    | .inr u=>Quotient.mk _ (.inr u)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    cases x <;> rfl
  right_inv x := by
    cases x with
    | inl q => refine Quotient.inductionOn q ?_; intro x; rfl
    | inr u => rfl

theorem count_addFixed [Finite A] (P : Equiv.Perm A) : count (addFixed P)=count P+1 := by
  have hh := Nat.card_congr (fixedCycleEquiv P)
  simpa only [Nat.card_sum,Nat.card_unique,count] using hh

end PlanarHom.FinitePermutationCycles
