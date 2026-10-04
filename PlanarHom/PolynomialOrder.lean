import PlanarHom.MatrixEntryAsymptotics
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial coefficients imply actual asymptotic orders

These results turn exact, finite coefficient calculations into real Big-O
estimates. Vanishing coefficients are hypotheses on the input polynomial,
not assumptions about a matrix logarithm or its asymptotics.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics Polynomial

namespace PlanarHom.MatrixLogCoefficients

/-- A polynomial with zero coefficients below degree `n` is `O(t^n)` at zero. -/
theorem polynomial_eval_isBigO_pow (p : Polynomial ℝ) (n : ℕ)
    (hzero : ∀ k < n, p.coeff k = 0) :
    (fun t : ℝ => p.eval t) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
  have hterm : ∀ k : ℕ, (fun t : ℝ => p.coeff k * t ^ k) =O[𝓝 0]
      (fun t : ℝ => t ^ n) := by
    intro k
    by_cases hk : k < n
    · simpa only [hzero k hk, zero_mul] using
        (isBigO_zero (E' := ℝ) (fun t : ℝ => t ^ n) (𝓝 0))
    · exact (pow_isBigO_pow (Nat.le_of_not_gt hk)).const_mul_left (p.coeff k)
  have h := IsBigO.sum (s := Finset.range (p.natDegree + 1)) (fun k _ => hterm k)
  exact h.congr_left (fun t => (Polynomial.eval_eq_sum_range t).symm)

/-- Matching coefficients through degree `n-1` give an `O(t^n)` difference. -/
theorem polynomial_eval_sub_isBigO_pow (p q : Polynomial ℝ) (n : ℕ)
    (hcoeff : ∀ k < n, p.coeff k = q.coeff k) :
    (fun t : ℝ => p.eval t - q.eval t) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
  have h := polynomial_eval_isBigO_pow (p - q) n (fun k hk => by simp [hcoeff k hk])
  simpa only [Polynomial.eval_sub] using h

/-- The finite Taylor polynomial formed from the actual coefficients. -/
def polynomialTaylor (p : Polynomial ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range n, Polynomial.C (p.coeff k) * Polynomial.X ^ k

@[simp] theorem polynomialTaylor_coeff (p : Polynomial ℝ) (n k : ℕ) :
    (polynomialTaylor p n).coeff k = if k < n then p.coeff k else 0 := by
  simp [polynomialTaylor, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]

/-- The finite Taylor subtraction remainder has the expected actual order. -/
theorem polynomial_eval_sub_taylor_isBigO (p : Polynomial ℝ) (n : ℕ) :
    (fun t : ℝ => p.eval t - ∑ k ∈ Finset.range n, p.coeff k * t ^ k) =O[𝓝 0]
      (fun t : ℝ => t ^ n) := by
  have h := polynomial_eval_sub_isBigO_pow p (polynomialTaylor p n) n
    (fun k hk => by simp [hk])
  simpa [polynomialTaylor, Polynomial.eval_finset_sum] using h

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Evaluate each entry of a matrix of real polynomials. -/
def polynomialMatrixEval (P : Matrix V V (Polynomial ℝ)) (t : ℝ) : Matrix V V ℝ :=
  fun i j => (P i j).eval t

/-- Entrywise polynomial coefficient vanishing yields an operator-norm order. -/
theorem polynomial_matrix_eval_isBigO_pow (P : Matrix V V (Polynomial ℝ)) (n : ℕ)
    (hzero : ∀ i j k, k < n → (P i j).coeff k = 0) :
    polynomialMatrixEval P =O[𝓝 0]
      (fun t : ℝ => t ^ n) := by
  apply matrix_isBigO_of_entries
  intro i j
  exact polynomial_eval_isBigO_pow (P i j) n (hzero i j)

end PlanarHom.MatrixLogCoefficients
