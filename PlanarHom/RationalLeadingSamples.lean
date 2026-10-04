import PlanarHom.SparseMatrixLeading
import Mathlib.Data.Real.Archimedean

/-!
# Positive rational samples preserve even leading coefficients

For nonzero `t`, choose a positive rational strictly between `|t|` and
`|t| + t²`. This has a quadratic error and preserves every even leading
coefficient. No continuity of the rational choice, or analytic continuation
from rational parameters, is assumed or needed.
-/

noncomputable section
open scoped Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients

private theorem exists_positive_rational_sample (t : ℝ) (ht : t ≠ 0) :
    ∃ q : ℚ, |t| < (q : ℝ) ∧ (q : ℝ) < |t| + t ^ 2 := by
  apply exists_rat_btwn
  nlinarith [sq_pos_of_ne_zero ht]

/-- A positive rational approximation to absolute value with quadratic error. -/
def positiveRationalSample (t : ℝ) : ℚ :=
  if ht : t = 0 then 0 else (exists_positive_rational_sample t ht).choose

/-- The same rational sample viewed as a real parameter. -/
def rationalSampleReal (t : ℝ) : ℝ := (positiveRationalSample t : ℝ)

@[simp] theorem positiveRationalSample_zero : positiveRationalSample 0 = 0 := by
  simp [positiveRationalSample]

@[simp] theorem rationalSampleReal_zero : rationalSampleReal 0 = 0 := by
  simp [rationalSampleReal]

theorem rationalSampleReal_bounds {t : ℝ} (ht : t ≠ 0) :
    |t| < rationalSampleReal t ∧ rationalSampleReal t < |t| + t ^ 2 := by
  simpa only [rationalSampleReal, positiveRationalSample, dif_neg ht] using
    (exists_positive_rational_sample t ht).choose_spec

/-- Every nonzero input is sent to a strictly positive rational parameter. -/
theorem rationalSampleReal_pos {t : ℝ} (ht : t ≠ 0) : 0 < rationalSampleReal t :=
  (abs_pos.mpr ht).trans (rationalSampleReal_bounds ht).1

/-- The rational choice has an actual quadratic approximation error. -/
theorem rationalSampleReal_sub_abs_isBigO :
    (fun t => rationalSampleReal t - |t|) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  apply IsBigO.of_bound 1
  apply Eventually.of_forall
  intro t
  by_cases ht : t = 0
  · subst t; simp
  obtain ⟨hl, hu⟩ := rationalSampleReal_bounds ht
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hl), abs_of_nonneg (sq_nonneg t)]
  linarith

/-- The rational sample tends to zero at at most first order. -/
theorem rationalSampleReal_isBigO : rationalSampleReal =O[𝓝 0] (fun t : ℝ => t) := by
  have hrem := rationalSampleReal_sub_abs_isBigO.trans
    (pow_isBigO_pow (show 1 ≤ 2 by omega))
  have habs : (fun t : ℝ => |t|) =O[𝓝 0] (fun t : ℝ => t) :=
    (isBigO_refl (fun t : ℝ => t) (𝓝 0)).norm_left
  simp only [pow_one] at hrem
  simpa only [sub_add_cancel] using hrem.add habs

theorem rationalSampleReal_tendsto : Tendsto rationalSampleReal (𝓝 0) (𝓝 0) :=
  rationalSampleReal_isBigO.trans_tendsto tendsto_id

/-- Powers of first-order functions differing by `O(t²)` differ by `O(t^(s+1))`. -/
theorem pow_sub_pow_isBigO {f g : ℝ → ℝ}
    (hf : f =O[𝓝 0] (fun t : ℝ => t)) (hg : g =O[𝓝 0] (fun t : ℝ => t))
    (hdiff : (fun t => f t - g t) =O[𝓝 0] (fun t : ℝ => t ^ 2)) (s : ℕ) :
    (fun t => f t ^ s - g t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
  induction s with
  | zero => simpa using (isBigO_zero (E' := ℝ) (fun t : ℝ => t) (𝓝 0))
  | succ s ih =>
    have h₁ := hf.mul ih
    have h₂ := hdiff.mul (hg.pow s)
    have h₁' : (fun t => f t * (f t ^ s - g t ^ s)) =O[𝓝 0]
        (fun t : ℝ => t ^ (s + 1 + 1)) := by
      convert h₁ using 1
      ext t
      ring
    have h₂' : (fun t => (f t - g t) * g t ^ s) =O[𝓝 0]
        (fun t : ℝ => t ^ (s + 1 + 1)) := by
      convert h₂ using 1
      ext t
      ring
    convert h₁'.add h₂' using 1
    ext t
    simp only [pow_succ]
    ring

/-- The sampling error does not alter any even leading monomial. -/
theorem rationalSampleReal_pow_sub_isBigO (s : ℕ) (hs : Even s) :
    (fun t => rationalSampleReal t ^ s - t ^ s) =O[𝓝 0] (fun t : ℝ => t ^ (s + 1)) := by
  have habs : (fun t : ℝ => |t|) =O[𝓝 0] (fun t : ℝ => t) :=
    (isBigO_refl (fun t : ℝ => t) (𝓝 0)).norm_left
  simpa only [hs.pow_abs] using
    pow_sub_pow_isBigO rationalSampleReal_isBigO habs rationalSampleReal_sub_abs_isBigO s

/-- Any actual even-order leading coefficient survives positive rational sampling. -/
theorem leading_isBigO_comp_rationalSample {f : ℝ → ℝ} (a : ℝ) (n : ℕ) (hn : Even n)
    (hf : (fun t => f t - a * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1))) :
    (fun t => f (rationalSampleReal t) - a * t ^ n) =O[𝓝 0]
      (fun t : ℝ => t ^ (n + 1)) := by
  have hrem := (hf.comp_tendsto rationalSampleReal_tendsto).trans
    (rationalSampleReal_isBigO.pow (n + 1))
  have hpow := (rationalSampleReal_pow_sub_isBigO n hn).const_mul_left a
  convert hrem.add hpow using 1
  ext t
  simp only [Function.comp_apply]
  ring

end PlanarHom.MatrixLogCoefficients
