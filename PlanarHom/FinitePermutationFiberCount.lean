import PlanarHom.FinitePermutationCycleCount
import Mathlib.Data.Fintype.Sigma

/-! Literal cycle-count decomposition over any preserved finite fiber label. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FinitePermutationCycles
variable {A I : Type} [Fintype A] [Fintype I]

 def fiberPermutation (P : Equiv.Perm A) (label : A → I) (hp : ∀a,label (P a)=label a) (i : I) :
    Equiv.Perm {a : A // label a=i} where
  toFun a := ⟨P a.val,(hp a.val).trans a.property⟩
  invFun a := ⟨P.symm a.val,by have h := hp (P.symm a.val); rw [Equiv.apply_symm_apply] at h; exact h.symm.trans a.property⟩
  left_inv a := Subtype.ext (P.symm_apply_apply a.val)
  right_inv a := Subtype.ext (P.apply_symm_apply a.val)

 theorem fiber_iterate (P : Equiv.Perm A) (label : A → I) (hp : ∀a,label (P a)=label a)
    (i : I) (a : {a : A // label a=i}) (n : ℕ) :
    ((fiberPermutation P label hp i)^[n] a).val=P^[n] a.val := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply']; exact congrArg P ih

 theorem label_sameCycle (P : Equiv.Perm A) (label : A → I) (hp : ∀a,label (P a)=label a)
    {a b : A} (h : P.SameCycle a b) : label a=label b := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hi : ∀n,label (P^[n] a)=label a := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',hp,ih]
  have hh := hi n
  rw [Equiv.Perm.iterate_eq_pow,hn] at hh
  exact hh.symm

 theorem fiber_sameCycle_iff (P : Equiv.Perm A) (label : A → I) (hp : ∀a,label (P a)=label a)
    (i : I) (a b : {a : A // label a=i}) :
    (fiberPermutation P label hp i).SameCycle a b ↔ P.SameCycle a.val b.val := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),?_⟩
    have hh := congrArg Subtype.val hn
    rw [← Equiv.Perm.iterate_eq_pow,fiber_iterate] at hh
    simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hh
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),?_⟩
    apply Subtype.ext
    rw [zpow_natCast,← Equiv.Perm.iterate_eq_pow,fiber_iterate,Equiv.Perm.iterate_eq_pow,hn]

 def fiberCycleLift (P : Equiv.Perm A) (label : A → I) (hp : ∀a,label (P a)=label a)
    (i : I) : Quotient (Equiv.Perm.SameCycle.setoid (fiberPermutation P label hp i)) →
      Quotient (Equiv.Perm.SameCycle.setoid P) :=
  Quotient.map Subtype.val (fun a b h => (fiber_sameCycle_iff P label hp i a b).mp h)

 def fiberCycleEquiv (P : Equiv.Perm A) (label : A → I) (hp : ∀a,label (P a)=label a) :
    (Σi,Quotient (Equiv.Perm.SameCycle.setoid (fiberPermutation P label hp i))) ≃
      Quotient (Equiv.Perm.SameCycle.setoid P) :=
  Equiv.ofBijective (fun p => fiberCycleLift P label hp p.1 p.2) (by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩ h
      induction x using Quotient.inductionOn with
      | h a =>
        induction y using Quotient.inductionOn with
        | h b =>
          have hh : P.SameCycle a.val b.val := Quotient.exact h
          have hij : i=j := a.property.symm.trans ((label_sameCycle P label hp hh).trans b.property)
          subst j
          apply congrArg (Sigma.mk i)
          exact Quotient.sound ((fiber_sameCycle_iff P label hp i a b).mpr hh)
    · intro x
      induction x using Quotient.inductionOn with
      | h a => exact ⟨⟨label a,Quotient.mk _ ⟨a,rfl⟩⟩,rfl⟩)

 theorem count_eq_sum_fibers (P : Equiv.Perm A) (label : A → I) (hp : ∀a,label (P a)=label a) :
    count P=∑ i,count (fiberPermutation P label hp i) := by
  rw [count,← Nat.card_congr (fiberCycleEquiv P label hp),Nat.card_sigma]
  rfl
end PlanarHom.FinitePermutationCycles
