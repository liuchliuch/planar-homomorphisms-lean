import PlanarHom.EntropyCompletion
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Quantitative Taylor bounds for the genuine spectral matrix logarithm

The logarithm is `EntropyCompletion.matrixLog`, defined by continuous functional
calculus. The estimates below are obtained from the scalar logarithm estimate
and explicit unitary diagonalization, not from an assumed matrix series.
-/

noncomputable section
open scoped NNReal BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics

namespace PlanarHom.MatrixLogCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A uniform entry bound controls the infinity operator norm. -/
theorem norm_le_card_mul_of_entry_le (A : Matrix V V ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ i j, ‖A i j‖ ≤ C) : ‖A‖ ≤ Fintype.card V * C := by
  rw [Matrix.linfty_opNorm_def]
  have h : Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) ≤
      (Fintype.card V : ℝ≥0) * ⟨C, hC⟩ := by
    apply Finset.sup_le
    intro i hi
    calc
      ∑ j, ‖A i j‖₊ ≤ ∑ _j : V, (⟨C, hC⟩ : ℝ≥0) :=
        Finset.sum_le_sum (fun j _ => hA i j)
      _ = _ := by simp
  exact_mod_cast h

/-- A finite-dimensional norm bound for the real Hermitian functional calculus. -/
theorem norm_cfc_le_card_sq (Q : Matrix V V ℝ) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x ∈ spectrum ℝ Q, ‖f x‖ ≤ C) :
    ‖cfc f Q‖ ≤ (Fintype.card V : ℝ) ^ 2 * C := by
  let U := (hQ.eigenvectorUnitary : Matrix V V ℝ)
  have hU : U ∈ Matrix.unitaryGroup V ℝ := hQ.eigenvectorUnitary.property
  have hnormU : ‖U‖ ≤ Fintype.card V := by
    simpa using norm_le_card_mul_of_entry_le U zero_le_one
      (entry_norm_bound_of_unitary hU)
  have hnormStarU : ‖star U‖ ≤ Fintype.card V := by
    simpa using norm_le_card_mul_of_entry_le (star U) zero_le_one
      (entry_norm_bound_of_unitary (unitary.star_mem hU))
  have hdiag : ‖Matrix.diagonal (fun i => f (hQ.eigenvalues i))‖ ≤ C := by
    rw [Matrix.linfty_opNorm_diagonal, pi_norm_le_iff_of_nonneg hC]
    intro i
    exact hf _ (hQ.eigenvalues_mem_spectrum_real i)
  rw [hQ.cfc_eq, Matrix.IsHermitian.cfc]
  change ‖U * Matrix.diagonal (fun i => f (hQ.eigenvalues i)) * star U‖ ≤ _
  calc
    _ ≤ (‖U‖ * ‖Matrix.diagonal (fun i => f (hQ.eigenvalues i))‖) * ‖star U‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (Fintype.card V : ℝ) * C * Fintype.card V := by gcongr
    _ = _ := by ring

variable [Nonempty V]

/-- The first `n` terms of the noncommutative logarithm polynomial. -/
def logTaylor (Q : Matrix V V ℝ) (n : ℕ) : Matrix V V ℝ :=
  -∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)⁻¹ • (-Q) ^ (k + 1)

omit [Nonempty V] in
/-- Functional calculus respects the logarithm polynomial. -/
theorem cfc_logTaylor (Q : Matrix V V ℝ) (hQ : Q.IsHermitian) (n : ℕ) :
    cfc (fun x : ℝ => -∑ k ∈ Finset.range n, (-x) ^ (k + 1) / (k + 1)) Q =
      logTaylor Q n := by
  rw [cfc_neg]
  congr 1
  have hsum : (fun x : ℝ => ∑ k ∈ Finset.range n, (-x) ^ (k + 1) / (k + 1)) =
      ∑ k ∈ Finset.range n, (fun x : ℝ => (-x) ^ (k + 1) / (k + 1)) := by
    ext x; simp
  rw [hsum, cfc_sum _ Q _ (by intro k hk; fun_prop)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [div_eq_mul_inv, mul_comm _ ((k + 1 : ℝ)⁻¹)]
  rw [cfc_const_mul _ _ Q (by fun_prop),
    cfc_pow (fun x : ℝ => -x) (k + 1) Q (by fun_prop) (show IsSelfAdjoint Q from hQ)]
  simp only [cfc_neg_id Q (show IsSelfAdjoint Q from hQ), Nat.cast_add, Nat.cast_one]

/-- Shift the scalar logarithm before applying the functional calculus. -/
theorem matrixLog_one_add (Q : Matrix V V ℝ) (hQ : Q.IsHermitian)
    (hnorm : ‖Q‖ < 1) :
    EntropyCompletion.matrixLog (1 + Q) = cfc (fun x : ℝ => Real.log (1 + x)) Q := by
  have hcont : ContinuousOn Real.log ((fun x : ℝ => 1 + x) '' spectrum ℝ Q) := by
    apply Real.continuousOn_log.mono
    rintro y ⟨x, hx, rfl⟩
    have hb := spectrum.norm_le_norm_of_mem hx
    have habs : |x| < 1 := lt_of_le_of_lt hb hnorm
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hlow := (abs_lt.mp habs).1
    linarith
  change cfc Real.log (1 + Q) = cfc (fun x : ℝ => Real.log (1 + x)) Q
  rw [cfc_comp' Real.log (fun x : ℝ => 1 + x) Q hcont (by fun_prop) (show IsSelfAdjoint Q from hQ)]
  rw [cfc_const_add 1 (fun x : ℝ => x) Q (by fun_prop) (show IsSelfAdjoint Q from hQ), cfc_id' ℝ Q (show IsSelfAdjoint Q from hQ),
    map_one]

/-- Arbitrary-order Taylor remainder, in operator norm, for the actual matrix log. -/
theorem norm_matrixLog_sub_logTaylor_le (Q : Matrix V V ℝ) (hQ : Q.IsHermitian)
    (hnorm : ‖Q‖ < 1) (n : ℕ) :
    ‖EntropyCompletion.matrixLog (1 + Q) - logTaylor Q n‖ ≤
      (Fintype.card V : ℝ) ^ 2 * (‖Q‖ ^ (n + 1) / (1 - ‖Q‖)) := by
  have hcont : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (spectrum ℝ Q) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    have hb := spectrum.norm_le_norm_of_mem hx
    have habs : |x| < 1 := lt_of_le_of_lt hb hnorm
    have hlow := (abs_lt.mp habs).1
    linarith
  rw [matrixLog_one_add Q hQ hnorm, ← cfc_logTaylor Q hQ n,
    ← cfc_sub _ _ Q hcont (by fun_prop)]
  apply norm_cfc_le_card_sq Q hQ _ (div_nonneg (pow_nonneg (norm_nonneg Q) _) (sub_pos.mpr hnorm).le)
  intro x hx
  have hb : |x| ≤ ‖Q‖ := spectrum.norm_le_norm_of_mem hx
  have habs : |-x| < 1 := by simpa using hb.trans_lt hnorm
  have ht := Real.abs_log_sub_add_sum_range_le habs n
  have hbound : |x| ^ (n + 1) / (1 - |x|) ≤ ‖Q‖ ^ (n + 1) / (1 - ‖Q‖) := by
    gcongr
    exact sub_pos.mpr hnorm
  simp only [abs_neg] at ht
  simpa only [Real.norm_eq_abs, sub_neg_eq_add, sub_neg_eq_add, abs_neg, add_comm] using
    ht.trans hbound

omit [Nonempty V] in
@[simp] theorem logTaylor_one (Q : Matrix V V ℝ) : logTaylor Q 1 = Q := by
  simp [logTaylor]

omit [Nonempty V] in
@[simp] theorem logTaylor_two (Q : Matrix V V ℝ) :
    logTaylor Q 2 = Q - (2 : ℝ)⁻¹ • Q ^ 2 := by
  simp [logTaylor, Finset.sum_range_succ, show (1 + 1 : ℝ) = 2 by norm_num]
  abel

/-- The quadratic matrix-log remainder is bounded by a cubic norm. -/
theorem norm_matrixLog_quadratic_remainder_le (Q : Matrix V V ℝ)
    (hQ : Q.IsHermitian) (hnorm : ‖Q‖ ≤ 1 / 2) :
    ‖EntropyCompletion.matrixLog (1 + Q) - (Q - (2 : ℝ)⁻¹ • Q ^ 2)‖ ≤ (2 * (Fintype.card V : ℝ) ^ 2) * ‖Q‖ ^ 3 := by
  have hlt : ‖Q‖ < 1 := by linarith
  have h := norm_matrixLog_sub_logTaylor_le Q hQ hlt 2
  simp only [logTaylor_two, Nat.reduceAdd] at h
  apply h.trans
  have hd : 0 < 1 - ‖Q‖ := by linarith
  have hdiv : ‖Q‖ ^ 3 / (1 - ‖Q‖) ≤ 2 * ‖Q‖ ^ 3 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [pow_nonneg (norm_nonneg Q) 3]
  calc
    _ ≤ (Fintype.card V : ℝ) ^ 2 * (2 * ‖Q‖ ^ 3) := by gcongr
    _ = _ := by ring

/-- On a fixed half-ball the general Taylor remainder has a uniform constant. -/
theorem norm_matrixLog_sub_logTaylor_le_half (Q : Matrix V V ℝ)
    (hQ : Q.IsHermitian) (hnorm : ‖Q‖ ≤ 1 / 2) (n : ℕ) :
    ‖EntropyCompletion.matrixLog (1 + Q) - logTaylor Q n‖ ≤
      (2 * (Fintype.card V : ℝ) ^ 2) * ‖Q‖ ^ (n + 1) := by
  have hlt : ‖Q‖ < 1 := by linarith
  apply (norm_matrixLog_sub_logTaylor_le Q hQ hlt n).trans
  have hd : 0 < 1 - ‖Q‖ := by linarith
  have hdiv : ‖Q‖ ^ (n + 1) / (1 - ‖Q‖) ≤ 2 * ‖Q‖ ^ (n + 1) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [pow_nonneg (norm_nonneg Q) (n + 1)]
  calc
    _ ≤ (Fintype.card V : ℝ) ^ 2 * (2 * ‖Q‖ ^ (n + 1)) := by gcongr
    _ = _ := by ring

/-- Composition form of the actual logarithm Taylor estimate along any curve. -/
theorem matrixLog_sub_logTaylor_isBigO {α : Type*} {l : Filter α}
    (Q : α → Matrix V V ℝ) (hQ : ∀ᶠ t in l, (Q t).IsHermitian)
    (hzero : Tendsto Q l (𝓝 0)) (n : ℕ) :
    (fun t => EntropyCompletion.matrixLog (1 + Q t) - logTaylor (Q t) n) =O[l]
      (fun t => ‖Q t‖ ^ (n + 1)) := by
  have hsmall : ∀ᶠ t in l, ‖Q t‖ < 1 / 2 := by
    apply Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
    simpa using hzero.norm
  apply IsBigO.of_bound (2 * (Fintype.card V : ℝ) ^ 2)
  filter_upwards [hQ, hsmall] with t ht hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using
    norm_matrixLog_sub_logTaylor_le_half (Q t) ht hs.le n

/-- If a Hermitian perturbation is `O(t^r)`, the actual logarithm remainder
after degree `n` is `O(t^(r*(n+1)))`. -/
theorem matrixLog_sub_logTaylor_isBigO_pow (Q : ℝ → Matrix V V ℝ)
    (hQ : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian) (hzero : Tendsto Q (𝓝 0) (𝓝 0))
    (r n : ℕ) (horder : Q =O[𝓝 0] (fun t : ℝ => t ^ r)) :
    (fun t => EntropyCompletion.matrixLog (1 + Q t) - logTaylor (Q t) n) =O[𝓝 0]
      (fun t : ℝ => t ^ (r * (n + 1))) := by
  have h := (matrixLog_sub_logTaylor_isBigO Q hQ hzero n).trans (horder.norm_left.pow (n + 1))
  simpa only [← pow_mul] using h

/-- The precise cubic-remainder order used for the Wheatstone gadget in Lemma 4.4. -/
theorem matrixLog_quadratic_remainder_isBigO_six (Q : ℝ → Matrix V V ℝ)
    (hQ : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian) (hzero : Tendsto Q (𝓝 0) (𝓝 0))
    (horder : Q =O[𝓝 0] (fun t : ℝ => t ^ 2)) :
    (fun t => EntropyCompletion.matrixLog (1 + Q t) -
      (Q t - (2 : ℝ)⁻¹ • Q t ^ 2)) =O[𝓝 0] (fun t : ℝ => t ^ 6) := by
  simpa only [logTaylor_two, Nat.reduceAdd, Nat.reduceMul] using
    matrixLog_sub_logTaylor_isBigO_pow Q hQ hzero 2 2 horder

end PlanarHom.MatrixLogCoefficients
