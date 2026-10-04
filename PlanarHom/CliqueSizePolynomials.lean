import PlanarHom.HammingKernelSquares
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Multiplicity

/-! NEW size-separating scalar polynomials for actual two-edge clique kernels. -/
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators Polynomial
namespace PlanarHom.CliqueSizePolynomials
open Polynomial

def diagonal (k : ℕ) : ℝ[X] := 1 + C ((k:ℝ)-1) * X^2

def offDiagonal (k : ℕ) : ℝ[X] := C 2 * X + C ((k:ℝ)-2) * X^2

/-- A monic associate of the size-k diagonal polynomial. -/
def primeFactor (k : ℕ) : ℝ[X] := X^2 + C (((k:ℝ)-1)⁻¹)

theorem factor_degree (k : ℕ) : (primeFactor k).natDegree = 2 := by
  simp [primeFactor]

theorem factor_monic (k : ℕ) : (primeFactor k).Monic := by
  exact monic_X_pow_add_C _ (by decide)

theorem factor_positive {k : ℕ} (hk : 2 ≤ k) (t : ℝ) :
    0 < (primeFactor k).eval t := by
  have hk' : 0 < (k:ℝ)-1 := by exact_mod_cast (show 0 < (k:ℤ)-1 by omega)
  simp only [primeFactor, eval_add, eval_pow, eval_X, eval_C]
  exact add_pos_of_nonneg_of_pos (sq_nonneg t) (inv_pos.mpr hk')

theorem factor_irreducible {k : ℕ} (hk : 2 ≤ k) : Irreducible (primeFactor k) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [factor_degree]
  · intro t ht
    exact (ne_of_gt (factor_positive hk t)) ht

theorem factor_prime {k : ℕ} (hk : 2 ≤ k) : Prime (primeFactor k) :=
  (factor_irreducible hk).prime

theorem diagonal_eq_factor {k : ℕ} (hk : 2 ≤ k) :
    diagonal k = C ((k:ℝ)-1) * primeFactor k := by
  have hk' : (k:ℝ)-1 ≠ 0 := by exact_mod_cast (show (k:ℤ)-1 ≠ 0 by omega)
  simp only [diagonal, primeFactor, mul_add, ← C_mul, mul_inv_cancel₀ hk', C_1]
  ring

theorem offDiagonal_eq_linear (k : ℕ) :
    offDiagonal k = X * (C 2 + C ((k:ℝ)-2)*X) := by
  unfold offDiagonal
  ring

theorem factor_not_dvd_constant {s : ℕ} (a : ℝ) (ha : a ≠ 0) :
    ¬ primeFactor s ∣ C a := by
  intro h
  have hd := natDegree_le_of_dvd h (C_ne_zero.mpr ha)
  simpa [factor_degree] using hd

theorem factor_not_dvd_X (s : ℕ) : ¬ primeFactor s ∣ (X : ℝ[X]) := by
  intro h
  have hd := natDegree_le_of_dvd h X_ne_zero
  simpa [factor_degree] using hd

theorem factor_not_dvd_linear (s k : ℕ) :
    ¬ primeFactor s ∣ (C 2 + C ((k:ℝ)-2)*X : ℝ[X]) := by
  intro h
  have hn : (C 2 + C ((k:ℝ)-2)*X : ℝ[X]) ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun p : ℝ[X] => p.coeff 0) hz
    norm_num at hz0
  have hd := natDegree_le_of_dvd h hn
  have hb : (C 2 + C ((k:ℝ)-2)*X : ℝ[X]).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    simp only [natDegree_C, zero_le, max_eq_right]
    simpa only [pow_one] using natDegree_C_mul_X_pow_le ((k:ℝ)-2) 1
  rw [factor_degree] at hd
  omega

theorem factor_not_dvd_offDiagonal {s : ℕ} (hs : 2 ≤ s) (k : ℕ) :
    ¬ primeFactor s ∣ offDiagonal k := by
  rw [offDiagonal_eq_linear]
  intro h
  rcases (factor_prime hs).dvd_or_dvd h with h|h
  · exact factor_not_dvd_X s h
  · exact factor_not_dvd_linear s k h

theorem factor_dvd_factor_iff (s k : ℕ) : primeFactor s ∣ primeFactor k ↔ s=k := by
  constructor
  · intro h
    have he := eq_of_monic_of_dvd_of_natDegree_le (factor_monic s) (factor_monic k) h
      (by simp [factor_degree])
    have hc := congrArg (fun p : ℝ[X] => p.coeff 0) he
    norm_num [primeFactor] at hc
    exact hc.symm
  · rintro rfl
    exact dvd_rfl

end PlanarHom.CliqueSizePolynomials
