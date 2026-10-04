import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite rigidity from three even power sums

This file proves the finite real-algebra step underlying Lemma 4.3 of
Liu--Meng. For strictly positive entries, the moments of orders `2`, `4`,
and `6` already force the rigidity used in that argument. The proof sums
the nonnegative quantities `a i ^ 2 * (a i ^ 2 - A ^ 2) ^ 2`; no limit
argument is needed.

This is only the finite power-sum implication. In particular, the analytic
hypotheses of Lemma 4.3 and the extraction of these moment identities from
those hypotheses are not asserted here.
-/

open scoped BigOperators

namespace PlanarHom.PowerSumRigidity

variable {I : Type*} [Fintype I]

/-- Three even moments concentrated at a positive value force every positive
entry to equal that value, and recover the number of entries. The parameter
`h` need not be assumed positive: the conclusion determines it. -/
theorem positive_three_even_moments_rigid
    (a : I → ℝ) (A h : ℝ) (ha : ∀ i, 0 < a i) (hA : 0 < A)
    (h2 : (∑ i, a i ^ 2) = h * A ^ 2)
    (h4 : (∑ i, a i ^ 4) = h * A ^ 4)
    (h6 : (∑ i, a i ^ 6) = h * A ^ 6) :
    (∀ i, a i = A) ∧ (Fintype.card I : ℝ) = h := by
  classical
  have hsum : (∑ i, a i ^ 2 * (a i ^ 2 - A ^ 2) ^ 2) = 0 := by
    calc
      (∑ i, a i ^ 2 * (a i ^ 2 - A ^ 2) ^ 2) =
          (∑ i, a i ^ 6) - 2 * A ^ 2 * (∑ i, a i ^ 4) +
            A ^ 4 * (∑ i, a i ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [h2, h4, h6]; ring
  have hnonneg : ∀ i, 0 ≤ a i ^ 2 * (a i ^ 2 - A ^ 2) ^ 2 :=
    fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hzero : ∀ i, a i ^ 2 * (a i ^ 2 - A ^ 2) ^ 2 = 0 := by
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => hnonneg i)).mp hsum i (Finset.mem_univ i)
  have heq : ∀ i, a i = A := by
    intro i
    have hsquare : (a i ^ 2 - A ^ 2) ^ 2 = 0 :=
      (mul_eq_zero.mp (hzero i)).resolve_left (pow_ne_zero _ (ne_of_gt (ha i)))
    exact (sq_eq_sq₀ (le_of_lt (ha i)) (le_of_lt hA)).mp
      (sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare))
  refine ⟨heq, ?_⟩
  have hcard : (Fintype.card I : ℝ) * A ^ 2 = h * A ^ 2 := by
    simpa only [heq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h2
  exact mul_right_cancel₀ (pow_ne_zero _ (ne_of_gt hA)) hcard

/-- If the average with positive denominator `h` has the same power sums
at orders `2`, `4`, and `6`, every entry equals this average and `h` is the
cardinality. Nonemptiness is essential here: an empty family has all power
sums zero for every positive denominator. -/
theorem positive_power_sum_rigidity [Nonempty I]
    (a : I → ℝ) (h : ℝ) (ha : ∀ i, 0 < a i) (hh : 0 < h)
    (h2 : ((∑ i, a i) / h) ^ 2 = (∑ i, a i ^ 2) / h)
    (h4 : ((∑ i, a i) / h) ^ 4 = (∑ i, a i ^ 4) / h)
    (h6 : ((∑ i, a i) / h) ^ 6 = (∑ i, a i ^ 6) / h) :
    (∀ i, a i = (∑ j, a j) / h) ∧ (Fintype.card I : ℝ) = h := by
  classical
  have hsum : 0 < ∑ i, a i :=
    Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  apply positive_three_even_moments_rigid a ((∑ i, a i) / h) h ha (div_pos hsum hh)
  · simpa only [mul_comm] using ((eq_div_iff (ne_of_gt hh)).mp h2).symm
  · simpa only [mul_comm] using ((eq_div_iff (ne_of_gt hh)).mp h4).symm
  · simpa only [mul_comm] using ((eq_div_iff (ne_of_gt hh)).mp h6).symm

/-- The all-positive-even-powers hypothesis used in the paper implies the
same finite rigidity. Only its instances at `2`, `4`, and `6` are needed. -/
theorem positive_even_power_sum_rigidity [Nonempty I]
    (a : I → ℝ) (h : ℝ) (ha : ∀ i, 0 < a i) (hh : 0 < h)
    (hpowers : ∀ s : ℕ, 0 < s → Even s →
      ((∑ i, a i) / h) ^ s = (∑ i, a i ^ s) / h) :
    (∀ i, a i = (∑ j, a j) / h) ∧ (Fintype.card I : ℝ) = h := by
  exact positive_power_sum_rigidity a h ha hh
    (hpowers 2 (by decide) ⟨1, rfl⟩)
    (hpowers 4 (by decide) ⟨2, rfl⟩)
    (hpowers 6 (by decide) ⟨3, rfl⟩)

end PlanarHom.PowerSumRigidity
