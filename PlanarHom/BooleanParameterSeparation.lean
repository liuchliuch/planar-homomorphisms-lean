import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A common odd exponent separating Boolean parameter classes

This module proves the finite parameter-separation step before equation (5.3),
on pages 46–47 of the paper. The parameters are actual real numbers, and the
exponent is a natural number; the negative power is the inverse of the positive
power.

Instead of the paper's hyperbolic-function argument, we prove that distinct
unequal-diagonal parameter pairs are separated at every sufficiently large
natural exponent. This gives the same required existence of one positive odd
exponent. We do not assert the stronger source claim that a pair collides at
most once. The upper bound `w < 1` is unnecessary for this separation step.
This is a supporting lemma, not the hardness or tractability theorem 5.1.
-/

noncomputable section

open Filter
open scoped Topology

namespace PlanarHom.BooleanParameterSeparation

/-- The real branch-point parameter `(θ^t - θ^(-t)) / (2w)`. -/
def beta (θ w : ℝ) (t : ℕ) : ℝ := (θ ^ t - (θ ^ t)⁻¹) / (2 * w)

/-- Agreement with the source's notation `β = a / w`, where
`a = (θ^t - θ^(-t)) / 2`. -/
theorem beta_eq_half_difference_div (θ w : ℝ) (t : ℕ) :
    beta θ w t = ((θ ^ t - (θ ^ t)⁻¹) / 2) / w := by
  simp only [beta, div_div]

/-- An unequal-diagonal class has strictly positive branch-point parameter
at every positive exponent. -/
theorem beta_pos {θ w : ℝ} {t : ℕ} (hθ : 1 < θ) (hw : 0 < w) (ht : 0 < t) :
    0 < beta θ w t := by
  have hp : 1 < θ ^ t := one_lt_pow₀ hθ (Nat.ne_of_gt ht)
  have hi : (θ ^ t)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  exact div_pos (sub_pos.mpr (hi.trans hp)) (mul_pos (by norm_num) hw)

/-- Equal diagonal parameters are separated precisely by their weights;
identical parameter pairs remain one class. -/
theorem beta_eq_iff_weight_eq {θ w v : ℝ} {t : ℕ}
    (hθ : 1 < θ) (hw : 0 < w) (hv : 0 < v) (ht : 0 < t) :
    beta θ w t = beta θ v t ↔ w = v := by
  have hp : 1 < θ ^ t := one_lt_pow₀ hθ (Nat.ne_of_gt ht)
  have ha : θ ^ t - (θ ^ t)⁻¹ ≠ 0 :=
    ne_of_gt (sub_pos.mpr ((inv_lt_one_of_one_lt₀ hp).trans hp))
  constructor
  · intro h
    have h' := (div_eq_div_iff (by positivity : (2 : ℝ) * w ≠ 0)
      (by positivity : (2 : ℝ) * v ≠ 0)).mp h
    have h'' : 2 * v = 2 * w := (mul_left_cancel₀ ha h')
    linarith
  · rintro rfl
    rfl

/-- Dividing by a comparison exponential gives a difference of two geometric
sequences. This identity uses ordinary real powers and inverses. -/
theorem beta_div_pow (θ w b : ℝ) (t : ℕ) :
    beta θ w t / b ^ t =
      ((θ / b) ^ t - (θ⁻¹ / b) ^ t) / (2 * w) := by
  simp only [beta, div_pow, inv_pow]
  ring

/-- A smaller base contributes zero after normalization by a larger base. -/
theorem tendsto_beta_div_larger_pow {θ w b : ℝ}
    (hθ : 1 < θ) (hθb : θ < b) :
    Tendsto (fun t : ℕ => beta θ w t / b ^ t) atTop (𝓝 0) := by
  have hb : 0 < b := (zero_lt_one.trans hθ).trans hθb
  have hratio : θ / b < 1 := (div_lt_one hb).mpr hθb
  have hiratio : θ⁻¹ / b < 1 :=
    (div_lt_one hb).mpr ((inv_lt_one_of_one_lt₀ hθ).trans (hθ.trans hθb))
  have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (zero_lt_one.trans hθ).le hb.le) hratio
  have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (inv_nonneg.mpr (zero_lt_one.trans hθ).le) hb.le) hiratio
  simpa only [beta_div_pow, sub_zero, zero_div] using (h₁.sub h₂).div_const (2 * w)

/-- A class normalized by its own exponential tends to a positive constant. -/
theorem tendsto_beta_div_own_pow {θ w : ℝ} (hθ : 1 < θ) :
    Tendsto (fun t : ℕ => beta θ w t / θ ^ t) atTop (𝓝 (1 / (2 * w))) := by
  have hpos : 0 < θ := zero_lt_one.trans hθ
  have hratio : θ⁻¹ / θ < 1 :=
    (div_lt_one hpos).mpr ((inv_lt_one_of_one_lt₀ hθ).trans hθ)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (inv_nonneg.mpr hpos.le) hpos.le) hratio
  simpa only [beta_div_pow, div_self (ne_of_gt hpos), one_pow, sub_zero] using
    (tendsto_const_nhds.sub h).div_const (2 * w)

/-- Distinct diagonal parameters have different eventual growth rates,
regardless of the positive weights. -/
theorem eventually_beta_lt_of_theta_lt {θ w b v : ℝ}
    (hθ : 1 < θ) (hθb : θ < b) (hv : 0 < v) :
    ∀ᶠ t : ℕ in atTop, beta θ w t < beta b v t := by
  have hb : 1 < b := hθ.trans hθb
  have h := (tendsto_beta_div_larger_pow (w := w) hθ hθb).eventually_lt
    (tendsto_beta_div_own_pow (w := v) hb) (by positivity : (0 : ℝ) < 1 / (2 * v))
  filter_upwards [h] with t ht
  exact (div_lt_div_iff_of_pos_right (pow_pos (zero_lt_one.trans hb) t)).mp ht

/-- Distinct parameter pairs with unequal diagonals are eventually separated.
No collision bound or separation hypothesis is assumed. -/
theorem eventually_beta_ne_of_parameters_ne {θ w b v : ℝ}
    (hθ : 1 < θ) (hb : 1 < b) (hw : 0 < w) (hv : 0 < v)
    (hne : (θ, w) ≠ (b, v)) :
    ∀ᶠ t : ℕ in atTop, beta θ w t ≠ beta b v t := by
  rcases lt_trichotomy θ b with hlt | heq | hgt
  · exact (eventually_beta_lt_of_theta_lt hθ hlt hv).mono fun _ h => ne_of_lt h
  · subst b
    have hwv : w ≠ v := fun h => hne (by rw [h])
    exact (eventually_gt_atTop 0).mono fun _ ht =>
      fun h => hwv ((beta_eq_iff_weight_eq hθ hw hv ht).mp h)
  · exact (eventually_beta_lt_of_theta_lt hb hgt hw).mono fun _ h => (ne_of_lt h).symm

/-- Equal pairs represent one class. Only the classes with `θ > 1` must have
distinct `beta` values; all equal-diagonal classes have `beta = 0`. -/
def Separates {ι : Type*} (s : Finset ι) (θ w : ι → ℝ) (t : ℕ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, 1 < θ i → 1 < θ j →
    (beta (θ i) (w i) t = beta (θ j) (w j) t ↔ (θ i, w i) = (θ j, w j))

/-- A finite family is simultaneously separated at all sufficiently large
natural exponents, including when the indexing repeats parameter pairs. -/
theorem eventually_separates {ι : Type*} (s : Finset ι) (θ w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    ∀ᶠ t : ℕ in atTop, Separates s θ w t := by
  unfold Separates
  refine (eventually_all_finset s).mpr fun i hi => ?_
  refine (eventually_all_finset s).mpr fun j hj => ?_
  by_cases hθi : 1 < θ i
  · by_cases hθj : 1 < θ j
    · by_cases heq : (θ i, w i) = (θ j, w j)
      · have heqθ : θ i = θ j := congrArg Prod.fst heq
        have heqw : w i = w j := congrArg Prod.snd heq
        exact Eventually.of_forall fun _ _ _ =>
          ⟨fun _ => heq, fun _ => by rw [heqθ, heqw]⟩
      · filter_upwards [eventually_beta_ne_of_parameters_ne hθi hθj
          (hw i hi) (hw j hj) heq] with t ht
        exact fun _ _ => ⟨fun h => (ht h).elim, fun h => (heq h).elim⟩
    · exact Eventually.of_forall fun _ _ h => (hθj h).elim
  · exact Eventually.of_forall fun _ h _ => (hθi h).elim

/-- Source's finite selection conclusion, strengthened to allow an arbitrary
prescribed lower bound. No representatives need be chosen first, and repeated
pairs remain precisely the same class. -/
theorem exists_positive_odd_separating_above {ι : Type*} (s : Finset ι)
    (θ w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) (lower : ℕ) :
    ∃ t : ℕ, lower ≤ t ∧ 0 < t ∧ Odd t ∧ Separates s θ w t := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_separates s θ w hw)
  refine ⟨2 * (N + lower) + 1, by omega, by omega,
    odd_two_mul_add_one (N + lower), hN _ (by omega)⟩

/-- There is a fixed positive odd natural exponent separating every distinct
unequal-diagonal parameter class of a finite family. -/
theorem exists_positive_odd_separating {ι : Type*} (s : Finset ι)
    (θ w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    ∃ t : ℕ, 0 < t ∧ Odd t ∧ Separates s θ w t := by
  obtain ⟨t, _, ht, ho, hs⟩ := exists_positive_odd_separating_above s θ w hw 0
  exact ⟨t, ht, ho, hs⟩

/-- The branch parameter vanishes identically for equal diagonal entries. -/
@[simp] theorem beta_one (w : ℝ) (t : ℕ) : beta 1 w t = 0 := by
  simp [beta]

/-- All source parameters have nonnegative branch-point parameters. -/
theorem beta_nonneg {θ w : ℝ} {t : ℕ}
    (hθ : 1 ≤ θ) (hw : 0 < w) (ht : 0 < t) : 0 ≤ beta θ w t := by
  rcases hθ.eq_or_lt with heq | hlt
  · rw [← heq, beta_one]
  · exact (beta_pos hlt hw ht).le

/-- A direct finite-set interface for the distinct parameter pairs. The source
assumptions `θ ≥ 1` and `w > 0` also give positivity exactly on the selected
unequal-diagonal classes. -/
theorem exists_positive_odd_injOn (s : Finset (ℝ × ℝ))
    (hθ : ∀ p ∈ s, 1 ≤ p.1) (hw : ∀ p ∈ s, 0 < p.2) :
    ∃ t : ℕ, 0 < t ∧ Odd t ∧
      (∀ p ∈ s, 0 ≤ beta p.1 p.2 t) ∧
      (∀ p ∈ s, 1 < p.1 → 0 < beta p.1 p.2 t) ∧
      Set.InjOn (fun p : ℝ × ℝ => beta p.1 p.2 t) {p | p ∈ s ∧ 1 < p.1} := by
  obtain ⟨t, ht, ho, hs⟩ := exists_positive_odd_separating s Prod.fst Prod.snd hw
  refine ⟨t, ht, ho, ?_, ?_, ?_⟩
  · exact fun p hp => beta_nonneg (hθ p hp) (hw p hp) ht
  · exact fun p hp hgt => beta_pos hgt (hw p hp) ht
  · intro p hp q hq heq
    exact (hs p hp.1 q hq.1 hp.2 hq.2).mp heq

/-- Representative interface: if a finite set of indices contains at most one
representative of each parameter pair, its unequal-diagonal representatives
have pairwise distinct branch parameters at a common positive odd exponent. -/
theorem exists_positive_odd_representatives {ι : Type*} (G : Finset ι)
    (θ w : ι → ℝ) (hw : ∀ i ∈ G, 0 < w i)
    (hrep : Set.InjOn (fun i => (θ i, w i)) (↑G : Set ι)) :
    ∃ t : ℕ, 0 < t ∧ Odd t ∧
      (∀ i ∈ G, 1 < θ i → 0 < beta (θ i) (w i) t) ∧
      Set.InjOn (fun i => beta (θ i) (w i) t) {i | i ∈ G ∧ 1 < θ i} := by
  obtain ⟨t, ht, ho, hs⟩ := exists_positive_odd_separating G θ w hw
  refine ⟨t, ht, ho, fun i hi hgt => beta_pos hgt (hw i hi) ht, ?_⟩
  intro i hi j hj heq
  exact hrep hi.1 hj.1 ((hs i hi.1 j hj.1 hi.2 hj.2).mp heq)

end PlanarHom.BooleanParameterSeparation
