import PlanarHom.SparseExponentialLeading
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Third-order matrix approximation arithmetic

All remainders are operator-norm Big-O estimates for actual real matrix curves.
The finite polynomial identities preserve multiplication order throughout.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixCubicApproximation
open MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matrix-valued cubic polynomial with fixed coefficients. -/
def cubic (A₀ A₁ A₂ A₃ : Matrix V V ℝ) (t : ℝ) : Matrix V V ℝ :=
  A₀ + t • A₁ + t ^ 2 • A₂ + t ^ 3 • A₃

/-- Exact noncommutative multiplication, including all discarded higher degrees. -/
theorem cubic_mul (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Matrix V V ℝ) (t : ℝ) :
    cubic A₀ A₁ A₂ A₃ t * cubic B₀ B₁ B₂ B₃ t =
      cubic (A₀ * B₀) (A₀ * B₁ + A₁ * B₀)
        (A₀ * B₂ + A₁ * B₁ + A₂ * B₀)
        (A₀ * B₃ + A₁ * B₂ + A₂ * B₁ + A₃ * B₀) t +
      t ^ 4 • (A₁ * B₃ + A₂ * B₂ + A₃ * B₁) +
      t ^ 5 • (A₂ * B₃ + A₃ * B₂) + t ^ 6 • (A₃ * B₃) := by
  simp only [cubic, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add]
  module

/-- A matrix monomial has its stated order. -/
theorem monomial_isBigO (A : Matrix V V ℝ) (n : ℕ) :
    (fun t : ℝ => t ^ n • A) =O[𝓝 0] (fun t : ℝ => t ^ n) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight A).isBigO_comp (fun t : ℝ => t ^ n) (𝓝 0)

/-- Every fixed matrix cubic is locally bounded. -/
theorem cubic_isBigO_one (A₀ A₁ A₂ A₃ : Matrix V V ℝ) :
    cubic A₀ A₁ A₂ A₃ =O[𝓝 0] (fun _t : ℝ => (1 : ℝ)) := by
  have hc : Continuous (cubic A₀ A₁ A₂ A₃) := by unfold cubic; fun_prop
  exact (hc.tendsto (0 : ℝ)).isBigO_one ℝ

/-- A curve with a cubic approximation is locally bounded. -/
theorem isBigO_one_of_cubic {f : ℝ → Matrix V V ℝ} (A₀ A₁ A₂ A₃ : Matrix V V ℝ)
    (hf : (fun t => f t - cubic A₀ A₁ A₂ A₃ t) =O[𝓝 0] (fun t : ℝ => t ^ 4)) :
    f =O[𝓝 0] (fun _t : ℝ => (1 : ℝ)) := by
  have hrem := hf.trans (pow_isBigO_pow (show 0 ≤ 4 by omega))
  simp only [pow_zero] at hrem
  simpa only [sub_add_cancel] using hrem.add (cubic_isBigO_one A₀ A₁ A₂ A₃)

/-- Multiplying actual cubic expansions gives the noncommutative convolution
of their coefficients, with a genuinely fourth-order remainder. -/
theorem mul_cubic_remainder_isBigO {f g : ℝ → Matrix V V ℝ}
    (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Matrix V V ℝ)
    (hf : (fun t => f t - cubic A₀ A₁ A₂ A₃ t) =O[𝓝 0] (fun t : ℝ => t ^ 4))
    (hg : (fun t => g t - cubic B₀ B₁ B₂ B₃ t) =O[𝓝 0] (fun t : ℝ => t ^ 4)) :
    (fun t => f t * g t -
      cubic (A₀ * B₀) (A₀ * B₁ + A₁ * B₀)
        (A₀ * B₂ + A₁ * B₁ + A₂ * B₀)
        (A₀ * B₃ + A₁ * B₂ + A₂ * B₁ + A₃ * B₀) t) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
  have h₁ := hf.mul (isBigO_one_of_cubic B₀ B₁ B₂ B₃ hg)
  have h₂ := (cubic_isBigO_one A₀ A₁ A₂ A₃).mul hg
  simp only [mul_one] at h₁
  simp only [one_mul] at h₂
  have hprod : (fun t => f t * g t -
      cubic A₀ A₁ A₂ A₃ t * cubic B₀ B₁ B₂ B₃ t) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
    convert h₁.add h₂ using 1
    funext t
    noncomm_ring
  have h₄ := monomial_isBigO (A₁ * B₃ + A₂ * B₂ + A₃ * B₁) 4
  have h₅ := (monomial_isBigO (A₂ * B₃ + A₃ * B₂) 5).trans
    (pow_isBigO_pow (show 4 ≤ 5 by omega))
  have h₆ := (monomial_isBigO (A₃ * B₃) 6).trans
    (pow_isBigO_pow (show 4 ≤ 6 by omega))
  have hpoly : (fun t => cubic A₀ A₁ A₂ A₃ t * cubic B₀ B₁ B₂ B₃ t -
      cubic (A₀ * B₀) (A₀ * B₁ + A₁ * B₀)
        (A₀ * B₂ + A₁ * B₁ + A₂ * B₀)
        (A₀ * B₃ + A₁ * B₂ + A₂ * B₁ + A₃ * B₀) t) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
    convert (h₄.add h₅).add h₆ using 1
    funext t
    rw [cubic_mul]
    abel
  simpa only [sub_add_sub_cancel] using hprod.add hpoly

/-- The actual matrix exponential has its ordinary cubic approximation. -/
theorem exp_cubic_remainder_isBigO (A : Matrix V V ℝ) :
    (fun t : ℝ => NormedSpace.exp ℝ (t • A) -
      cubic 1 A ((1 / 2 : ℝ) • A ^ 2) ((1 / 6 : ℝ) • A ^ 3) t) =O[𝓝 0]
      (fun t : ℝ => t ^ 4) := by
  have h := exp_sub_expTaylor_isBigO A 4
  convert h using 1
  funext t
  congr 1
  norm_num [expTaylor, cubic, Finset.sum_range_succ, Nat.factorial]
  module

end PlanarHom.MatrixCubicApproximation
