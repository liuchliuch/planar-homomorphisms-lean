import PlanarHom.FinitePermutationCycleSigns
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! NEW product of literal per-cycle Kasteleyn signs. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FinitePermutationCycles
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev CycleClass (P : Equiv.Perm A) := Quotient (Equiv.Perm.SameCycle.setoid P)
noncomputable instance (P : Equiv.Perm A) : Fintype (CycleClass P) := Fintype.ofFinite _

def classOf (P : Equiv.Perm A) (a : A) : CycleClass P := Quotient.mk _ a

def CycleProductLaw (P : Equiv.Perm A) (w : A→ℤ) : Prop :=
  ∀q : CycleClass P,(∏a : {a // classOf P a=q},w a)=
    (-1:ℤ)^(Fintype.card {a // classOf P a=q}+1)

theorem product_eq_sign (P : Equiv.Perm A) (w : A→ℤ) (h : CycleProductLaw P w) :
    (∏a,w a)=(Equiv.Perm.sign P : ℤ) := by
  unfold CycleProductLaw at h
  rw [←Fintype.prod_fiberwise (classOf P) w]
  simp_rw [h]
  rw [Finset.prod_pow_eq_pow_sum,Finset.sum_add_distrib]
  have hc : (∑q : CycleClass P,Fintype.card {a // classOf P a=q})=Fintype.card A := by
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
      (Fintype.sum_fiberwise (classOf P) (fun _=>1 : A→ℕ))
  rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
  rw [sign_coe_eq_pow_card_add_count]
  congr 2
  exact (Nat.card_eq_fintype_card).symm

/-- Transfer a product law along the actual inclusion of an invariant carrier.
This is used to keep exactly the faces on the derived true side. -/
theorem cycleProductLaw_subtype (P : Equiv.Perm A) (w : A→ℤ)
    (p : A→Prop) [DecidablePred p] (hp : ∀a,p (P a) ↔ p a)
    (h : ∀q : CycleClass P,(∃a,p a ∧ classOf P a=q) →
      (∏a : {a // classOf P a=q},w a)=(-1:ℤ)^(Fintype.card {a // classOf P a=q}+1)) :
    CycleProductLaw (P.subtypePerm hp) (fun a=>w a.val) := by
  intro q
  induction q using Quotient.inductionOn with | h a =>
    let target : CycleClass P := classOf P a.val
    have hall : ∀b : A,classOf P b=target → p b := by
      intro b hb
      have hs : P.SameCycle a.val b := (Quotient.exact hb).symm
      obtain ⟨n,hn⟩ := hs.exists_nat_pow_eq
      have hi : ∀n,p (P^[n] a.val) := by
        intro n
        induction n with
        | zero => exact a.property
        | succ n ih => rw [Function.iterate_succ_apply']; exact (hp _).mpr ih
      simpa only [Equiv.Perm.iterate_eq_pow,hn] using hi n
    let e : {b : {x // p x} // classOf (P.subtypePerm hp) b=classOf (P.subtypePerm hp) a} ≃
        {b : A // classOf P b=target} :=
      { toFun := fun b=>⟨b.val.val,Quotient.sound
          (Equiv.Perm.sameCycle_subtypePerm.mp (Quotient.exact b.property))⟩
        invFun := fun b=>⟨⟨b.val,hall b.val b.property⟩,Quotient.sound
          (Equiv.Perm.sameCycle_subtypePerm.mpr (Quotient.exact b.property))⟩
        left_inv := by intro b; rfl
        right_inv := by intro b; rfl }
    have hh := h target ⟨a.val,a.property,rfl⟩
    change (∏b : {b : {x // p x} // classOf (P.subtypePerm hp) b=classOf (P.subtypePerm hp) a},w b.val.val)=_
    rw [←Fintype.card_congr e] at hh
    rw [←e.prod_comp (fun b=>w b.val)] at hh
    exact hh

end PlanarHom.FinitePermutationCycles
