import PlanarHom.PolynomialOrder

/-!
# Fifth-order expansion of the logarithm of a polynomial matrix perturbation

For a Hermitian polynomial perturbation whose entries start at degree two,
all log coefficients through degree five are the actual coefficients of
`P - P²/2`. This combines exact polynomial arithmetic with the analytic
remainder theorem for the genuine spectral matrix logarithm.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics Polynomial
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Evaluation commutes with ordinary matrix multiplication. -/
theorem polynomialMatrixEval_mul (P R : Matrix V V (Polynomial ℝ)) (t : ℝ) :
    polynomialMatrixEval (P * R) t = polynomialMatrixEval P t * polynomialMatrixEval R t := by
  ext i j
  simp [polynomialMatrixEval, Matrix.mul_apply, Polynomial.eval_finset_sum]

/-- The exact polynomial supplying logarithmic coefficients through degree five. -/
def quadraticLogPolynomial (P : Matrix V V (Polynomial ℝ)) : Matrix V V (Polynomial ℝ) :=
  fun i j => P i j - Polynomial.C (2 : ℝ)⁻¹ * (P ^ 2) i j

/-- Evaluate the exact quadratic log polynomial. -/
theorem polynomialMatrixEval_quadraticLogPolynomial (P : Matrix V V (Polynomial ℝ)) (t : ℝ) :
    polynomialMatrixEval (quadraticLogPolynomial P) t =
      polynomialMatrixEval P t - (2 : ℝ)⁻¹ • (polynomialMatrixEval P t) ^ 2 := by
  have hmul := polynomialMatrixEval_mul P P t
  ext i j
  simp only [polynomialMatrixEval, quadraticLogPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  congr 1
  simpa only [pow_two, polynomialMatrixEval] using
    congrArg (fun A : Matrix V V ℝ => A i j) hmul

/-- Coefficients of the explicit quadratic logarithm polynomial. -/
theorem quadraticLogPolynomial_coeff (P : Matrix V V (Polynomial ℝ)) (i j : V) (k : ℕ) :
    (quadraticLogPolynomial P i j).coeff k =
      (P i j).coeff k - (2 : ℝ)⁻¹ * ((P ^ 2) i j).coeff k := by
  simp [quadraticLogPolynomial, Polynomial.coeff_C_mul]

variable [Nonempty V]

/-- Vanishing constant and linear coefficients are sufficient for the exact
polynomial `P-P²/2` to approximate the genuine log with error `O(t⁶)`. -/
theorem matrixLog_polynomial_quadratic_remainder_isBigO (P : Matrix V V (Polynomial ℝ))
    (hcoeff : ∀ i j k, k < 2 → (P i j).coeff k = 0)
    (hherm : ∀ᶠ t in 𝓝 0, (polynomialMatrixEval P t).IsHermitian) :
    (fun t => EntropyCompletion.matrixLog (1 + polynomialMatrixEval P t) -
      polynomialMatrixEval (quadraticLogPolynomial P) t) =O[𝓝 0] (fun t : ℝ => t ^ 6) := by
  have horder := polynomial_matrix_eval_isBigO_pow P 2 hcoeff
  have hzero : Tendsto (polynomialMatrixEval P) (𝓝 0) (𝓝 0) :=
    horder.trans_tendsto (by simpa using (continuous_pow 2).tendsto (0 : ℝ))
  simpa only [polynomialMatrixEval_quadraticLogPolynomial] using
    matrixLog_quadratic_remainder_isBigO_six (polynomialMatrixEval P) hherm hzero horder

/-- All actual logarithmic coefficients below degree six are computed from
`P-P²/2`, not assumed as expansion hypotheses. -/
theorem matrixLog_polynomial_entry_sub_taylor_isBigO (P : Matrix V V (Polynomial ℝ))
    (hcoeff : ∀ i j k, k < 2 → (P i j).coeff k = 0)
    (hherm : ∀ᶠ t in 𝓝 0, (polynomialMatrixEval P t).IsHermitian) (i j : V) :
    (fun t => EntropyCompletion.matrixLog (1 + polynomialMatrixEval P t) i j -
      ∑ k ∈ Finset.range 6,
        ((P i j).coeff k - (2 : ℝ)⁻¹ * ((P ^ 2) i j).coeff k) * t ^ k)
      =O[𝓝 0] (fun t : ℝ => t ^ 6) := by
  have hlog := entry_isBigO (matrixLog_polynomial_quadratic_remainder_isBigO P hcoeff hherm) i j
  have hpoly := polynomial_eval_sub_taylor_isBigO (quadraticLogPolynomial P i j) 6
  have h := hlog.add hpoly
  simpa only [Matrix.sub_apply, polynomialMatrixEval, sub_add_sub_cancel,
    quadraticLogPolynomial_coeff] using h

/-- More conveniently, any explicitly matched polynomial through degree five
is a valid logarithmic expansion with an `O(t⁶)` remainder. -/
theorem matrixLog_polynomial_entry_sub_eval_isBigO (P : Matrix V V (Polynomial ℝ))
    (hcoeff : ∀ i j k, k < 2 → (P i j).coeff k = 0)
    (hherm : ∀ᶠ t in 𝓝 0, (polynomialMatrixEval P t).IsHermitian)
    (i j : V) (p : Polynomial ℝ)
    (hmatch : ∀ k < 6,
      (P i j).coeff k - (2 : ℝ)⁻¹ * ((P ^ 2) i j).coeff k = p.coeff k) :
    (fun t => EntropyCompletion.matrixLog (1 + polynomialMatrixEval P t) i j - p.eval t)
      =O[𝓝 0] (fun t : ℝ => t ^ 6) := by
  have hlog := entry_isBigO (matrixLog_polynomial_quadratic_remainder_isBigO P hcoeff hherm) i j
  have hpoly := polynomial_eval_sub_isBigO_pow (quadraticLogPolynomial P i j) p 6
    (fun k hk => by simpa only [quadraticLogPolynomial_coeff] using hmatch k hk)
  have h := hlog.add hpoly
  simpa only [Matrix.sub_apply, polynomialMatrixEval, sub_add_sub_cancel] using h

end PlanarHom.MatrixLogCoefficients
