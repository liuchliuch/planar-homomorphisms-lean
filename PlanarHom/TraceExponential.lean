import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import PlanarHom.TracePositivity

/-!
# The differential of the trace of the matrix exponential

All exponentials in this file are the genuine matrix exponential `NormedSpace.exp`.
The matrices in the first-derivative formulas need not commute. Termwise
differentiation is justified by locally uniform, summable operator-norm bounds.
The Hessian is strictly positive in every nonzero Hermitian direction at every
Hermitian base point; a scalar identity shift reduces this to termwise positivity
at PSD points.
-/

open scoped BigOperators Matrix.Norms.Operator RightActions ComplexOrder
open Matrix

noncomputable section

namespace PlanarHom
namespace TraceExponential

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix trace as a continuous linear map. -/
def traceCLM : Matrix ι ι ℝ →L[ℝ] ℝ :=
  ⟨Matrix.traceLinearMap ι ℝ ℝ, continuous_id.matrix_trace⟩

omit [DecidableEq ι] in
@[simp] theorem traceCLM_apply (A : Matrix ι ι ℝ) : traceCLM A = A.trace := rfl

/-- The trace pairing, bundled continuously in both arguments. -/
def tracePairing : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Matrix ι ι ℝ) (Matrix ι ι ℝ) ℝ traceCLM).comp
    (ContinuousLinearMap.mul ℝ (Matrix ι ι ℝ))

omit [DecidableEq ι] in
@[simp] theorem tracePairing_apply (A V : Matrix ι ι ℝ) :
    tracePairing A V = (A * V).trace := rfl

/-- Cyclicity removes the location of the differentiated factor in a matrix power. -/
theorem trace_power_insert (A V : Matrix ι ι ℝ) (n i : ℕ) (hi : i ≤ n) :
    (A ^ (n - i) * V * A ^ i).trace = (A ^ n * V).trace := by
  rw [Matrix.trace_mul_cycle, ← pow_add, Nat.add_sub_of_le hi]

/-- The trace of a positive matrix power has its expected differential, without
any commutation assumption on the perturbation. -/
theorem hasFDerivAt_trace_pow_succ (A : Matrix ι ι ℝ) (n : ℕ) :
    HasFDerivAt (fun X : Matrix ι ι ℝ => (X ^ (n + 1)).trace)
      ((n + 1 : ℝ) • tracePairing (A ^ n)) A := by
  convert (traceCLM (ι := ι)).hasFDerivAt.comp A (hasFDerivAt_pow' (𝕜 := ℝ) (n + 1)) using 1
  ext V
  simp only [ContinuousLinearMap.comp_apply, traceCLM_apply, ContinuousLinearMap.smul_apply,
    tracePairing_apply, smul_eq_mul, ContinuousLinearMap.sum_apply,
    Nat.add_sub_cancel, Nat.pred_eq_sub_one]
  simp only [ContinuousLinearMap.id_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, Matrix.trace_sum]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (A ^ (n - i) * V * A ^ i).trace = (A ^ n * V).trace := by
    intro i hi
    exact trace_power_insert A V n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  rw [Finset.sum_congr rfl hterm]
  simp

/-- Termwise differential of the shifted trace-exponential series. -/
theorem hasFDerivAt_trace_exp_term (A : Matrix ι ι ℝ) (n : ℕ) :
    HasFDerivAt
      (fun X : Matrix ι ι ℝ => ((n + 1).factorial : ℝ)⁻¹ * (X ^ (n + 1)).trace)
      ((n.factorial : ℝ)⁻¹ • tracePairing (A ^ n)) A := by
  have h := (hasFDerivAt_trace_pow_succ A n).const_smul
    (((n + 1).factorial : ℝ)⁻¹)
  have hc : ((n + 1).factorial : ℝ)⁻¹ * (n + 1 : ℝ) = (n.factorial : ℝ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, _root_.mul_inv_rev]
    rw [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  simpa only [smul_eq_mul, smul_smul, hc] using h

/-- A summable scalar bound for the local derivative series. -/
theorem summable_exp_derivative_bound (r C : ℝ) (hr : 0 ≤ r) :
    Summable (fun n : ℕ => C * ((n.factorial : ℝ)⁻¹ * r ^ n)) := by
  have h := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) r
  simp only [smul_eq_mul, norm_mul, norm_inv, norm_natCast, norm_pow,
    Real.norm_eq_abs, abs_of_nonneg hr] at h
  exact h.mul_left C

/-- A uniform derivative bound on a ball about the origin. -/
theorem norm_trace_exp_term_derivative_le (X : Matrix ι ι ℝ) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (hX : ‖X‖ ≤ r) :
    ‖(n.factorial : ℝ)⁻¹ • tracePairing (X ^ n)‖ ≤
      ‖(tracePairing (ι := ι))‖ * ((n.factorial : ℝ)⁻¹ * r ^ n) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hz : tracePairing (X ^ n) = 0 := by
      ext V
      simp [tracePairing_apply, Matrix.trace]
    rw [hz, smul_zero, norm_zero]
    positivity
  rw [norm_smul, norm_inv, norm_natCast]
  calc
    (n.factorial : ℝ)⁻¹ * ‖tracePairing (X ^ n)‖
        ≤ (n.factorial : ℝ)⁻¹ * (‖(tracePairing (ι := ι))‖ * ‖X ^ n‖) :=
      mul_le_mul_of_nonneg_left ((tracePairing (ι := ι)).le_opNorm _) (by positivity)
    _ ≤ (n.factorial : ℝ)⁻¹ * (‖(tracePairing (ι := ι))‖ * r ^ n) := by
      gcongr
      exact (norm_pow_le X n).trans (pow_le_pow_left₀ (norm_nonneg X) hX n)
    _ = _ := by ring

/-- The actual exponential series remains summable after taking trace. -/
theorem hasSum_trace_exp (A : Matrix ι ι ℝ) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (A ^ n).trace)
      (NormedSpace.exp ℝ A).trace := by
  simpa only [traceCLM_apply, map_smul, smul_eq_mul] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).mapL (traceCLM (ι := ι))

/-- Summing the differentiated coefficients gives trace pairing against `exp A`. -/
theorem hasSum_trace_exp_derivative (A : Matrix ι ι ℝ) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • tracePairing (A ^ n))
      (tracePairing (NormedSpace.exp ℝ A)) := by
  simpa only [map_smul] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).mapL (tracePairing (ι := ι))

/-- The differential of trace exponential on all real matrices. No symmetry or
commutation hypothesis is needed. -/
theorem hasFDerivAt_trace_exp (A : Matrix ι ι ℝ) :
    HasFDerivAt (fun X : Matrix ι ι ℝ => (NormedSpace.exp ℝ X).trace)
      (tracePairing (NormedSpace.exp ℝ A)) A := by
  let r : ℝ := ‖A‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hA : A ∈ Metric.ball (0 : Matrix ι ι ℝ) r := by
    simp [Metric.mem_ball, dist_zero_right, r]
  have hsum := hasFDerivAt_tsum_of_isPreconnected
    (summable_exp_derivative_bound r ‖(tracePairing (ι := ι))‖ hr.le)
    Metric.isOpen_ball (convex_ball (0 : Matrix ι ι ℝ) r).isPreconnected
    (fun n X _ => hasFDerivAt_trace_exp_term X n)
    (fun n X hX => norm_trace_exp_term_derivative_le X n hr.le
      (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hX)))
    hA ((hasSum_trace_exp A).summable.comp_injective Nat.succ_injective) hA
  rw [(hasSum_trace_exp_derivative A).tsum_eq] at hsum
  have hfun : (fun X : Matrix ι ι ℝ =>
      ∑' n : ℕ, ((n + 1).factorial : ℝ)⁻¹ * (X ^ (n + 1)).trace) =
      (fun X => (NormedSpace.exp ℝ X).trace - (1 : Matrix ι ι ℝ).trace) := by
    funext X
    have h := (hasSum_trace_exp X).summable.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one,
      pow_zero, one_mul, (hasSum_trace_exp X).tsum_eq] at h
    linarith
  rw [hfun] at hsum
  simpa only [sub_add_cancel] using hsum.add_const ((1 : Matrix ι ι ℝ).trace)

/-- Pointwise form of the Fréchet derivative. -/
theorem fderiv_trace_exp (A V : Matrix ι ι ℝ) :
    fderiv ℝ (fun X : Matrix ι ι ℝ => (NormedSpace.exp ℝ X).trace) A V =
      (NormedSpace.exp ℝ A * V).trace := by
  rw [(hasFDerivAt_trace_exp A).fderiv, tracePairing_apply]

/-- The directional derivative along an arbitrary affine line of matrices. -/
theorem hasDerivAt_trace_exp_line (A V : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp ℝ (A + s • V)).trace)
      (NormedSpace.exp ℝ (A + t • V) * V).trace t := by
  simpa only [Function.comp_def, tracePairing_apply, id_eq, one_smul] using
    (hasFDerivAt_trace_exp (A + t • V)).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const V).const_add A)

/-- The matrix-valued gradient of trace exponential is differentiable at zero;
its derivative is the trace bilinear pairing. -/
theorem hasFDerivAt_trace_exp_gradient_zero :
    HasFDerivAt
      (fun X : Matrix ι ι ℝ =>
        fderiv ℝ (fun Y : Matrix ι ι ℝ => (NormedSpace.exp ℝ Y).trace) X)
      (tracePairing (ι := ι)) 0 := by
  have h : HasFDerivAt (fun X : Matrix ι ι ℝ => tracePairing (NormedSpace.exp ℝ X))
      (tracePairing (ι := ι)) 0 := by
    simpa using (tracePairing (ι := ι)).hasFDerivAt.comp 0
      (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix ι ι ℝ))
  have hf : (fun X : Matrix ι ι ℝ =>
      fderiv ℝ (fun Y : Matrix ι ι ℝ => (NormedSpace.exp ℝ Y).trace) X) =
      (fun X => tracePairing (NormedSpace.exp ℝ X)) := by
    funext X
    exact (hasFDerivAt_trace_exp X).fderiv
  rw [hf]
  exact h

/-- The Hessian of trace exponential at zero is `Tr(V W)`. -/
theorem second_fderiv_trace_exp_zero (V W : Matrix ι ι ℝ) :
    fderiv ℝ
      (fun X : Matrix ι ι ℝ =>
        fderiv ℝ (fun Y : Matrix ι ι ℝ => (NormedSpace.exp ℝ Y).trace) X) 0 V W =
      (V * W).trace := by
  rw [hasFDerivAt_trace_exp_gradient_zero.fderiv, tracePairing_apply]

omit [DecidableEq ι] in
/-- The trace pairing is positive definite on real Hermitian matrices. -/
theorem trace_square_pos {V : Matrix ι ι ℝ} (hV : V.IsHermitian) (hne : V ≠ 0) :
    0 < (V * V).trace := by
  have hnonneg := (Matrix.posSemidef_conjTranspose_mul_self V).trace_nonneg
  have hne' : (Vᴴ * V).trace ≠ 0 := by
    exact fun h => hne (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h)
  simpa only [hV.eq] using lt_of_le_of_ne hnonneg (Ne.symm hne')

/-- Strict positivity of the Hessian at the origin in every nonzero symmetric direction. -/
theorem second_fderiv_trace_exp_zero_pos {V : Matrix ι ι ℝ}
    (hV : V.IsHermitian) (hne : V ≠ 0) :
    0 < fderiv ℝ
      (fun X : Matrix ι ι ℝ =>
        fderiv ℝ (fun Y : Matrix ι ι ℝ => (NormedSpace.exp ℝ Y).trace) X) 0 V V := by
  rw [second_fderiv_trace_exp_zero]
  exact trace_square_pos hV hne

/-- The noncommutative derivative of the `(n+1)`st exponential term. -/
def expDerivativeTerm (A : Matrix ι ι ℝ) (n : ℕ) :
    Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ :=
  ((n + 1).factorial : ℝ)⁻¹ •
    ∑ i ∈ Finset.range (n + 1),
      ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℝ) (A ^ (n - i)) (A ^ i)

@[simp] theorem expDerivativeTerm_apply (A V : Matrix ι ι ℝ) (n : ℕ) :
    expDerivativeTerm A n V = ((n + 1).factorial : ℝ)⁻¹ •
      ∑ i ∈ Finset.range (n + 1), A ^ (n - i) * V * A ^ i := by
  simp [expDerivativeTerm]

/-- Termwise differentiation uses the full noncommutative power rule. -/
theorem hasFDerivAt_exp_term (A : Matrix ι ι ℝ) (n : ℕ) :
    HasFDerivAt
      (fun X : Matrix ι ι ℝ => ((n + 1).factorial : ℝ)⁻¹ • X ^ (n + 1))
      (expDerivativeTerm A n) A := by
  convert (hasFDerivAt_pow' (𝕜 := ℝ) (x := A) (n + 1)).const_smul
    (((n + 1).factorial : ℝ)⁻¹) using 1

/-- A locally uniform summable bound for the full matrix derivative series. -/
theorem norm_expDerivativeTerm_le (A : Matrix ι ι ℝ) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hA : ‖A‖ ≤ r) :
    ‖expDerivativeTerm A n‖ ≤ (n.factorial : ℝ)⁻¹ * r ^ n := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hz : expDerivativeTerm A n = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  have hp (k : ℕ) : ‖A ^ k‖ ≤ r ^ k :=
    (norm_pow_le A k).trans (pow_le_pow_left₀ (norm_nonneg A) hA k)
  have hs : ‖∑ i ∈ Finset.range (n + 1),
      ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℝ) (A ^ (n - i)) (A ^ i)‖ ≤
      (n + 1 : ℝ) * r ^ n := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          ‖ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℝ)
            (A ^ (n - i)) (A ^ i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), r ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ ‖A ^ (n - i)‖ * ‖A ^ i‖ :=
            ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le _ _ _ _
          _ ≤ r ^ (n - i) * r ^ i := mul_le_mul (hp _) (hp _) (norm_nonneg _) (by positivity)
          _ = r ^ n := by
            rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
      _ = _ := by simp
  rw [expDerivativeTerm, norm_smul, norm_inv, norm_natCast]
  calc
    _ ≤ ((n + 1).factorial : ℝ)⁻¹ * ((n + 1 : ℝ) * r ^ n) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        _root_.mul_inv_rev, ← mul_assoc, mul_assoc ((n.factorial : ℝ)⁻¹),
        inv_mul_cancel₀ (by positivity), mul_one]

/-- The full matrix exponential has the sum of the noncommutative termwise
power derivatives as its Fréchet derivative. -/
theorem hasFDerivAt_exp_series (A : Matrix ι ι ℝ) :
    HasFDerivAt (NormedSpace.exp ℝ : Matrix ι ι ℝ → Matrix ι ι ℝ)
      (∑' n : ℕ, expDerivativeTerm A n) A := by
  let r : ℝ := ‖A‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hA : A ∈ Metric.ball (0 : Matrix ι ι ℝ) r := by
    simp [Metric.mem_ball, dist_zero_right, r]
  have hu : Summable (fun n : ℕ => (n.factorial : ℝ)⁻¹ * r ^ n) := by
    simpa only [one_mul] using summable_exp_derivative_bound r 1 hr.le
  have hsum := hasFDerivAt_tsum_of_isPreconnected hu
    Metric.isOpen_ball (convex_ball (0 : Matrix ι ι ℝ) r).isPreconnected
    (fun n X _ => hasFDerivAt_exp_term X n)
    (fun n X hX => norm_expDerivativeTerm_le X n hr.le
      (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hX)))
    hA ((NormedSpace.expSeries_summable' (𝕂 := ℝ) A).comp_injective Nat.succ_injective) hA
  have hfun : (fun X : Matrix ι ι ℝ =>
      ∑' n : ℕ, ((n + 1).factorial : ℝ)⁻¹ • X ^ (n + 1)) =
      (fun X => NormedSpace.exp ℝ X - 1) := by
    funext X
    have h := (NormedSpace.expSeries_summable' (𝕂 := ℝ) X).sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one,
      pow_zero, one_smul, (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X).tsum_eq] at h
    exact eq_sub_of_add_eq' h
  rw [hfun] at hsum
  simpa only [sub_add_cancel] using hsum.add_const (1 : Matrix ι ι ℝ)

/-- The derivative series is genuinely summable, not just a formal identity. -/
theorem hasSum_expDerivativeTerm (A : Matrix ι ι ℝ) :
    HasSum (expDerivativeTerm A) (fderiv ℝ (NormedSpace.exp ℝ) A) := by
  rw [(hasFDerivAt_exp_series A).fderiv]
  apply Summable.hasSum
  apply Summable.of_norm_bounded
    (summable_exp_derivative_bound (‖A‖ + 1) 1 (by positivity))
  intro n
  simpa only [one_mul] using norm_expDerivativeTerm_le A n (by positivity)
    (le_add_of_nonneg_right zero_le_one)

/-- The Hessian is the derivative of the gradient `exp`, paired by trace. -/
theorem hasFDerivAt_trace_exp_gradient (A : Matrix ι ι ℝ) :
    HasFDerivAt
      (fun X : Matrix ι ι ℝ =>
        fderiv ℝ (fun Y : Matrix ι ι ℝ => (NormedSpace.exp ℝ Y).trace) X)
      ((tracePairing (ι := ι)).comp (fderiv ℝ (NormedSpace.exp ℝ) A)) A := by
  have h := (tracePairing (ι := ι)).hasFDerivAt.comp A
    (hasFDerivAt_exp_series A).differentiableAt.hasFDerivAt
  have hf : (fun X : Matrix ι ι ℝ =>
      fderiv ℝ (fun Y : Matrix ι ι ℝ => (NormedSpace.exp ℝ Y).trace) X) =
      (fun X => tracePairing (NormedSpace.exp ℝ X)) := by
    funext X
    exact (hasFDerivAt_trace_exp X).fderiv
  rw [hf]
  exact h

/-- Pointwise identification of the Hessian with the true matrix exponential derivative. -/
theorem second_fderiv_trace_exp (A V W : Matrix ι ι ℝ) :
    fderiv ℝ
      (fun X : Matrix ι ι ℝ =>
        fderiv ℝ (fun Y : Matrix ι ι ℝ => (NormedSpace.exp ℝ Y).trace) X) A V W =
      (fderiv ℝ (NormedSpace.exp ℝ) A V * W).trace := by
  rw [(hasFDerivAt_trace_exp_gradient A).fderiv]
  rfl

/-- The scalar series expressing a quadratic Hessian direction. -/
def hessianTerm (A V : Matrix ι ι ℝ) (n : ℕ) : ℝ :=
  ((n + 1).factorial : ℝ)⁻¹ *
    ∑ i ∈ Finset.range (n + 1), (A ^ (n - i) * V * A ^ i * V).trace

@[simp] theorem hessianTerm_zero (A V : Matrix ι ι ℝ) :
    hessianTerm A V 0 = (V * V).trace := by
  simp [hessianTerm]

/-- The Hessian series converges to the actual derivative, including noncommuting directions. -/
theorem hasSum_hessianTerm (A V : Matrix ι ι ℝ) :
    HasSum (hessianTerm A V) (fderiv ℝ (NormedSpace.exp ℝ) A V * V).trace := by
  have h := (hasSum_expDerivativeTerm A).mapL
    ((tracePairing V).comp (ContinuousLinearMap.apply ℝ (Matrix ι ι ℝ) V))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    tracePairing_apply, Matrix.trace_mul_comm V, expDerivativeTerm_apply,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.sum_mul,
    Matrix.trace_sum, hessianTerm] using h

/-- Translating by a scalar matrix multiplies the genuine matrix exponential by a scalar. -/
theorem exp_add_smul_one (A : Matrix ι ι ℝ) (c : ℝ) :
    NormedSpace.exp ℝ (A + c • (1 : Matrix ι ι ℝ)) =
      Real.exp c • NormedSpace.exp ℝ A := by
  have hc : Commute A (c • (1 : Matrix ι ι ℝ)) := by
    exact (Commute.one_right A).smul_right c
  rw [NormedSpace.exp_add_of_commute hc]
  have hexp : NormedSpace.exp ℝ (c • (1 : Matrix ι ι ℝ)) =
      Real.exp c • (1 : Matrix ι ι ℝ) := by
    have h := NormedSpace.map_exp (𝕂 := ℝ) (algebraMap ℝ (Matrix ι ι ℝ))
      (continuous_algebraMap ℝ (Matrix ι ι ℝ)) c
    simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using h.symm
  rw [hexp, Matrix.mul_smul, mul_one]

/-- Translating by a scalar matrix scales the full Fréchet derivative of matrix exponential. -/
theorem fderiv_exp_add_smul_one (A : Matrix ι ι ℝ) (c : ℝ) :
    fderiv ℝ (NormedSpace.exp ℝ) (A + c • (1 : Matrix ι ι ℝ)) =
      Real.exp c • fderiv ℝ (NormedSpace.exp ℝ) A := by
  have hleft := (hasFDerivAt_exp_series (A + c • (1 : Matrix ι ι ℝ))).differentiableAt.hasFDerivAt
    |>.comp A ((hasFDerivAt_id A).add_const (c • (1 : Matrix ι ι ℝ)))
  have hright := (hasFDerivAt_exp_series A).differentiableAt.hasFDerivAt.const_smul (Real.exp c)
  have hleft' : HasFDerivAt
      (fun X : Matrix ι ι ℝ => Real.exp c • NormedSpace.exp ℝ X)
      (fderiv ℝ (NormedSpace.exp ℝ) (A + c • (1 : Matrix ι ι ℝ))) A := by
    simpa only [Function.comp_def, exp_add_smul_one, ContinuousLinearMap.comp_id] using hleft
  exact hleft'.unique hright

/-- Every term of the quadratic Hessian series is nonnegative at a PSD base point. -/
theorem hessianTerm_nonneg {A V : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hV : V.IsHermitian) (n : ℕ) :
    0 ≤ hessianTerm A V n := by
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i hi
  exact TracePositivity.trace_pow_mul_direction_nonneg hA hV (n - i) i

/-- At PSD points the Hessian dominates the positive trace inner product. -/
theorem trace_square_le_trace_fderiv_exp_mul_self {A V : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hV : V.IsHermitian) :
    (V * V).trace ≤ (fderiv ℝ (NormedSpace.exp ℝ) A V * V).trace := by
  have h := (hasSum_hessianTerm A V).summable.le_tsum 0
    (fun n _ => hessianTerm_nonneg hA hV n)
  simpa only [hessianTerm_zero, (hasSum_hessianTerm A V).tsum_eq] using h

/-- Strict positivity of the actual Hessian quadratic form at every PSD point. -/
theorem trace_fderiv_exp_mul_self_pos_of_posSemidef {A V : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hV : V.IsHermitian) (hne : V ≠ 0) :
    0 < (fderiv ℝ (NormedSpace.exp ℝ) A V * V).trace :=
  (trace_square_pos hV hne).trans_le (trace_square_le_trace_fderiv_exp_mul_self hA hV)

/-- Global strict positivity of the exponential Hessian in symmetric directions.
The base matrix may have arbitrary positive and negative eigenvalues. -/
theorem trace_fderiv_exp_mul_self_pos {A V : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hV : V.IsHermitian) (hne : V ≠ 0) :
    0 < (fderiv ℝ (NormedSpace.exp ℝ) A V * V).trace := by
  obtain ⟨c, hc, hshift⟩ := TracePositivity.exists_nonneg_scalar_shift_posSemidef hA
  have h := trace_fderiv_exp_mul_self_pos_of_posSemidef hshift hV hne
  rw [fderiv_exp_add_smul_one, ContinuousLinearMap.smul_apply, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul] at h
  exact (mul_pos_iff_of_pos_left (Real.exp_pos c)).mp h

/-- The Hessian of trace exponential is positive definite on real Hermitian matrices
at every real Hermitian base point. -/
theorem second_fderiv_trace_exp_pos {A V : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hV : V.IsHermitian) (hne : V ≠ 0) :
    0 < fderiv ℝ
      (fun X : Matrix ι ι ℝ =>
        fderiv ℝ (fun Y : Matrix ι ι ℝ => (NormedSpace.exp ℝ Y).trace) X) A V V := by
  rw [second_fderiv_trace_exp]
  exact trace_fderiv_exp_mul_self_pos hA hV hne

/-- Trace exponential is real analytic on the entire matrix space. -/
theorem analyticAt_trace_exp (A : Matrix ι ι ℝ) :
    AnalyticAt ℝ (fun X : Matrix ι ι ℝ => (NormedSpace.exp ℝ X).trace) A := by
  exact ((traceCLM (ι := ι)).analyticAt _).comp (NormedSpace.exp_analytic A)

end TraceExponential
end PlanarHom
