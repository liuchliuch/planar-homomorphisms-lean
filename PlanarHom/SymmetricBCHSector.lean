import PlanarHom.SymmetricBCH
import PlanarHom.RationalLeadingSamples

/-!
# Extracting the symmetric BCH coefficient from a rational positive sector

Only two positive rational slopes are needed. Rational vanishing of the actual
spectral-log entries, together with the proved one-variable cubic expansions,
forces the double-commutator entry to vanish. No bivariate analyticity or
formal coefficient-vanishing hypothesis is used.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients

/-- An actual leading coefficient vanishes if the function is zero at zero
and at all sufficiently small positive rational parameters. -/
theorem leading_coefficient_zero_of_rational_zeros (f : ℝ → ℝ) (a : ℝ) (n : ℕ)
    (hzero : f 0 = 0)
    (hf : (fun t => f t - a * t ^ n) =O[𝓝 0] (fun t : ℝ => t ^ (n + 1)))
    (hrational : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε → f q = 0) :
    a = 0 := by
  obtain ⟨ε, hε, hrat⟩ := hrational
  have hsamplezero : ∀ᶠ t in 𝓝 0, f (rationalSampleReal t) = 0 := by
    filter_upwards [rationalSampleReal_tendsto.eventually_lt_const hε] with t ht
    by_cases htzero : t = 0
    · subst t; simpa only [rationalSampleReal_zero] using hzero
    · exact hrat (positiveRationalSample t) (rationalSampleReal_pos htzero) ht
  have hpow := pow_leading_isBigO a n 2 hf
  have heven : Even (n * 2) := ⟨n, by omega⟩
  have hsampled := leading_isBigO_comp_rationalSample (a ^ 2) (n * 2) heven hpow
  have hz : (fun t => f (rationalSampleReal t) ^ 2 - 0 * t ^ (n * 2)) =O[𝓝 0]
      (fun t : ℝ => t ^ (n * 2 + 1)) := by
    apply isBigO_of_eventually_zero
    filter_upwards [hsamplezero] with t ht
    simp [ht]
  have hsq := leading_coefficient_unique (a ^ 2) 0 (n * 2) hsampled hz
  exact (sq_eq_zero_iff).mp hsq

end PlanarHom.MatrixLogCoefficients

namespace PlanarHom.SymmetricBCH
open MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Rational vanishing of a nonedge entry determines the actual cubic
coefficient on one sector ray. -/
theorem sector_cubic_entry_zero_of_rational_log_zeros (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (η : ℝ) (i j : V)
    (hCij : C i j = 0) (hBij : B i j = 0)
    (hrational : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
      EntropyCompletion.matrixLog (sandwich C (η • B) (q : ℝ)) i j = 0) :
    (-η / 24) * commutator C (commutator C B) i j +
      (η ^ 2 / 12) * commutator B (commutator B C) i j = 0 := by
  let f : ℝ → ℝ := fun t => EntropyCompletion.matrixLog (sandwich C (η • B) t) i j
  have hf := entry_isBigO (matrixLog_symmetric_sector_cubic_remainder_isBigO C B hC hB η) i j
  have hzero : f 0 = 0 := by
    dsimp [f]
    rw [sandwich_zero]
    have hlog : EntropyCompletion.matrixLog (1 : Matrix V V ℝ) = 0 := CFC.log_one
    rw [hlog]
    rfl
  apply leading_coefficient_zero_of_rational_zeros f _ 3 hzero _ hrational
  convert hf using 1
  funext t
  simp only [f, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    hCij, hBij]
  ring

/-- Two distinct nonzero slopes identify both scalar double-commutator entries. -/
theorem double_coefficients_zero_of_two_slopes (D E a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h₁ : (-a / 24) * D + (a ^ 2 / 12) * E = 0)
    (h₂ : (-b / 24) * D + (b ^ 2 / 12) * E = 0) : D = 0 ∧ E = 0 := by
  have hf₁ : a * (-D + 2 * a * E) = 0 := by nlinarith [h₁]
  have hf₂ : b * (-D + 2 * b * E) = 0 := by nlinarith [h₂]
  have hr₁ := (mul_eq_zero.mp hf₁).resolve_left ha
  have hr₂ := (mul_eq_zero.mp hf₂).resolve_left hb
  have hdiff : (a - b) * E = 0 := by nlinarith
  have hE := (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hab)
  constructor
  · simpa only [hE, mul_zero, add_zero, neg_eq_zero] using hr₁
  · exact hE

/-- Positive rational sector vanishing of the actual logarithm forces the
`-[C,[C,B]]/24` coefficient to vanish, by comparing two rational sector rays. -/
theorem double_commutator_entry_zero_of_rational_sector (C B : Matrix V V ℝ)
    (hC : C.IsHermitian) (hB : B.IsHermitian) (i j : V)
    (hCij : C i j = 0) (hBij : B i j = 0) (η₀ : ℝ) (hη₀ : 0 < η₀)
    (hsector : ∀ η : ℚ, 0 < (η : ℝ) → (η : ℝ) < η₀ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
        EntropyCompletion.matrixLog (sandwich C ((η : ℝ) • B) (q : ℝ)) i j = 0) :
    commutator C (commutator C B) i j = 0 ∧
      commutator B (commutator B C) i j = 0 := by
  obtain ⟨η, hηpos, hηlt⟩ := exists_rat_btwn (show (0 : ℝ) < η₀ / 2 by linarith)
  have hη : (η : ℝ) < η₀ := by linarith
  have htwoηpos : 0 < ((2 * η : ℚ) : ℝ) := by norm_cast at *; positivity
  have htwoηlt : ((2 * η : ℚ) : ℝ) < η₀ := by push_cast; linarith
  have h₁ := sector_cubic_entry_zero_of_rational_log_zeros C B hC hB (η : ℝ) i j
    hCij hBij (hsector η hηpos hη)
  have h₂ := sector_cubic_entry_zero_of_rational_log_zeros C B hC hB ((2 * η : ℚ) : ℝ) i j
    hCij hBij (hsector (2 * η) htwoηpos htwoηlt)
  apply double_coefficients_zero_of_two_slopes _ _ (η : ℝ) ((2 * η : ℚ) : ℝ)
    (ne_of_gt hηpos) (ne_of_gt htwoηpos) _ h₁ h₂
  push_cast
  intro heq
  linarith

end PlanarHom.SymmetricBCH
