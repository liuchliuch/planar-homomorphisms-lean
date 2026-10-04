import PlanarHom.FinitePermutationCycleCount
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

/-! NEW exact permutation sign from the literal number of all cycles,
including fixed points. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {A : Type*} [Fintype A] [DecidableEq A]

private def cycleLabel (P : Equiv.Perm A) (a : A) :
    {x : A // P x=x} ⊕ P.cycleFactorsFinset :=
  if h : P a=a then .inl ⟨a,h⟩
  else .inr ⟨P.cycleOf a, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
    (Equiv.Perm.mem_support.mpr h)⟩

private theorem cycleLabel_eq_iff (P : Equiv.Perm A) (a b : A) :
    cycleLabel P a=cycleLabel P b ↔ P.SameCycle a b := by
  by_cases ha : P a=a <;> by_cases hb : P b=b
  · simp only [cycleLabel,dif_pos ha,dif_pos hb,Sum.inl.injEq,Subtype.mk.injEq]
    exact ⟨fun h=>h ▸ Equiv.Perm.SameCycle.rfl,fun h=>h.eq_of_left ha⟩
  · simp only [cycleLabel,dif_pos ha,dif_neg hb,Sum.inl_ne_inr,false_iff]
    exact fun h=>hb (h.apply_eq_self_iff.mp ha)
  · simp only [cycleLabel,dif_neg ha,dif_pos hb,Sum.inr_ne_inl,false_iff]
    exact fun h=>ha (h.apply_eq_self_iff.mpr hb)
  · simp only [cycleLabel,dif_neg ha,dif_neg hb,Sum.inr.injEq,Subtype.mk.injEq]
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
      (Equiv.Perm.mem_support.mpr ha) (Equiv.Perm.mem_support.mpr hb)).symm

private theorem cycleLabel_surjective (P : Equiv.Perm A) :
    Function.Surjective (cycleLabel P) := by
  intro x
  rcases x with a|c
  · exact ⟨a,by simp [cycleLabel,a.property]⟩
  · obtain ⟨a,ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
    have hpa : P a≠a := Equiv.Perm.mem_support.mp
      (Equiv.Perm.mem_cycleFactorsFinset_support_le c.property ha)
    refine ⟨a,?_⟩
    simp only [cycleLabel,dif_neg hpa,Sum.inr.injEq,Subtype.mk.injEq]
    apply Subtype.ext
    exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff P c.val c.property a).mpr ha |>.symm

private def cycleLabelEquiv (P : Equiv.Perm A) :
    Quotient (Equiv.Perm.SameCycle.setoid P) ≃
      ({x : A // P x=x} ⊕ P.cycleFactorsFinset) :=
  Equiv.ofBijective
    (Quotient.lift (cycleLabel P) (fun a b h=>(cycleLabel_eq_iff P a b).mpr h))
    ⟨by
      intro q r h
      induction q using Quotient.inductionOn with | h a =>
        induction r using Quotient.inductionOn with | h b =>
          exact Quotient.sound ((cycleLabel_eq_iff P a b).mp h),by
      intro x
      obtain ⟨a,ha⟩ := cycleLabel_surjective P x
      exact ⟨Quotient.mk _ a,ha⟩⟩

theorem count_eq_fixed_add_cycles (P : Equiv.Perm A) :
    count P=Fintype.card {a : A // P a=a}+P.cycleFactorsFinset.card := by
  rw [count,Nat.card_congr (cycleLabelEquiv P),Nat.card_eq_fintype_card,Fintype.card_sum]
  simp

theorem count_eq_fixed_add_cycleType (P : Equiv.Perm A) :
    count P=Fintype.card {a : A // P a=a}+P.cycleType.card := by
  rw [count_eq_fixed_add_cycles]
  simp [Equiv.Perm.cycleType_def]

/-- The plus form avoids truncated natural subtraction and applies to an empty
carrier as well as permutations with fixed points. -/
theorem sign_eq_pow_card_add_count (P : Equiv.Perm A) :
    Equiv.Perm.sign P=(-1:ℤˣ)^(Fintype.card A+count P) := by
  rw [Equiv.Perm.sign_of_cycleType,count_eq_fixed_add_cycleType]
  have hcard : Fintype.card {a : A // P a=a}+P.cycleType.sum=Fintype.card A := by
    have h := Equiv.Perm.card_fixedPoints P
    change Fintype.card {a : A // P a=a}=_ at h
    have hs : P.cycleType.sum≤Fintype.card A := by
      rw [Equiv.Perm.sum_cycleType]
      exact Finset.card_le_univ _
    omega
  have he : Fintype.card A+(Fintype.card {a : A // P a=a}+P.cycleType.card)=
      (P.cycleType.sum+P.cycleType.card)+2*Fintype.card {a : A // P a=a} := by omega
  rw [he]
  symm
  calc
    _ = (-1:ℤˣ)^(P.cycleType.sum+P.cycleType.card) * ((-1:ℤˣ)^2)^Fintype.card {a : A // P a=a} := by rw [pow_add,pow_mul]
    _ = _ := by norm_num

theorem sign_coe_eq_pow_card_add_count (P : Equiv.Perm A) :
    (Equiv.Perm.sign P : ℤ)=(-1:ℤ)^(Fintype.card A+count P) := by
  rw [sign_eq_pow_card_add_count]
  simp

/-- Count actual permutation cycles by any proved complete orbit label. -/
theorem count_eq_card_of_label {B : Type*} [Fintype B] (P : Equiv.Perm A)
    (label : A→B) (hsurj : Function.Surjective label)
    (heq : ∀a b,P.SameCycle a b ↔ label a=label b) : count P=Fintype.card B := by
  let e : Quotient (Equiv.Perm.SameCycle.setoid P)≃B :=
    Equiv.ofBijective (Quotient.lift label (fun a b h=>(heq a b).mp h))
      ⟨by
        intro a b h
        induction a using Quotient.inductionOn with | h a =>
          induction b using Quotient.inductionOn with | h b =>
            exact Quotient.sound ((heq a b).mpr h),by
        intro b
        obtain ⟨a,ha⟩ := hsurj b
        exact ⟨Quotient.mk _ a,ha⟩⟩
  exact (Nat.card_congr e).trans Nat.card_eq_fintype_card

end PlanarHom.FinitePermutationCycles
