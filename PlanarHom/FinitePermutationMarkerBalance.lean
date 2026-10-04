import PlanarHom.FinitePermutationFixedCycle
import PlanarHom.FinitePermutationCycleTransport
import PlanarHom.FinitePermutationSwapSplit
import Mathlib.GroupTheory.Perm.Option

/-! Deleting an inactive dart from an arbitrary collection of vertex cycles.
The change in rotation cycles is exactly the change in face cycles. There is
no assumption that the rotation consists of just one complete cyclic row. -/
noncomputable section
open Classical
namespace PlanarHom.FinitePermutationCycles
variable {A : Type} [Fintype A]

 theorem count_optionCongr (P : Equiv.Perm A) : count P.optionCongr=count P+1 := by
  have h := count_of_step P.optionCongr (addFixed P) (Equiv.optionEquivSumPUnit A)
    (by intro a; cases a <;> rfl)
  rw [h,count_addFixed]

 theorem optionCongr_mul (P Q : Equiv.Perm A) :
    (P*Q).optionCongr=P.optionCongr*Q.optionCongr := by
  apply Equiv.ext
  intro a
  cases a <;> rfl

 theorem removeNone_mul_fixed (R : Equiv.Perm (Option A)) (I : Equiv.Perm A) :
    Equiv.removeNone (R*I.optionCongr)=Equiv.removeNone R*I := by
  apply Equiv.optionCongr_injective
  rw [map_equiv_removeNone,optionCongr_mul,map_equiv_removeNone]
  have hi : (R*I.optionCongr) none=R none := rfl
  rw [hi,mul_assoc]

 theorem count_removeNone_fixed (P : Equiv.Perm (Option A)) (h : P none=none) :
    count (Equiv.removeNone P)+1=count P := by
  have he := map_equiv_removeNone P
  simp only [h,Equiv.swap_self,Equiv.Perm.coe_one,Equiv.Perm.one_def,Equiv.refl_trans] at he
  change (Equiv.removeNone P).optionCongr=P at he
  exact (count_optionCongr (Equiv.removeNone P)).symm.trans (congrArg count he)

 theorem count_removeNone_moving (P : Equiv.Perm (Option A)) (h : P none≠none) :
    count (Equiv.removeNone P)=count P := by
  have hn : P.symm none≠none := by
    intro he
    apply h
    have hh := congrArg P he
    simpa only [Equiv.apply_symm_apply] using hh.symm
  have hs : P.SameCycle (P.symm none) none := by
    have hh : P.SameCycle (P.symm none) (P (P.symm none)) :=
      Equiv.Perm.SameCycle.rfl.apply_right
    simpa only [Equiv.apply_symm_apply] using hh
  have hc := count_swap_of_same P (P.symm none) none hn hs
  have he : swapInput P (P.symm none) none=(Equiv.removeNone P).optionCongr := by
    rw [map_equiv_removeNone]
    apply Equiv.ext
    intro z
    simp only [swapInput,Equiv.trans_apply,Equiv.Perm.mul_apply]
    by_cases hz : z=P.symm none
    · subst z
      simp only [Equiv.swap_apply_left,Equiv.apply_symm_apply]
    · by_cases hz0 : z=none
      · subst z
        simp only [Equiv.swap_apply_right,Equiv.apply_symm_apply]
      · have hp0 : P z≠none := by
          intro h0
          exact hz (P.injective (h0.trans (P.apply_symm_apply none).symm))
        have hpn : P z≠P none := P.injective.ne hz0
        rw [@Equiv.swap_apply_of_ne_of_ne (Option A) (Classical.decEq _)
          (P.symm none) none z hz hz0,Equiv.swap_apply_of_ne_of_ne hp0 hpn]
  rw [he,count_optionCongr] at hc
  omega

/-- The singleton correction cancels between the vertex rotation and its
face permutation, including when the deleted marker is itself a whole row. -/
 theorem removeNone_count_balance (R : Equiv.Perm (Option A)) (I : Equiv.Perm A) :
    count (R*I.optionCongr)+count (Equiv.removeNone R)=
      count (Equiv.removeNone R*I)+count R := by
  have hm := removeNone_mul_fixed R I
  by_cases h : R none=none
  · have hR := count_removeNone_fixed R h
    have hF := count_removeNone_fixed (R*I.optionCongr) h
    rw [hm] at hF
    omega
  · have hR := count_removeNone_moving R h
    have hF := count_removeNone_moving (R*I.optionCongr) h
    rw [hm] at hF
    omega
end PlanarHom.FinitePermutationCycles
