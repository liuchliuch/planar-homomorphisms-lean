import PlanarHom.BooleanSquareRootIndependence
import PlanarHom.BooleanEigenvalueBranches

/-!
# Removing equal-diagonal factors from genuine ratio identities

The equal-diagonal branch on positive `x` is `w*x`. Its analytic extension
across zero is signed and yields an odd logarithm. The unequal-diagonal
positive square root yields an even analytic logarithm. Taking the even part
of the continued identity removes precisely the equal-diagonal classes.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace PlanarHom.BooleanRatioParity
open BooleanEigenvalueBranches BooleanSquareRootIndependence

/-- The extension across zero used only to establish identities. -/
def signedLog (c a w x : ℝ) : ℝ :=
  if a = 0 then Real.log (1 - w*x) - Real.log (1 + w*x)
  else logRatio c a w (x^2)

theorem square_parameter_bounds {w x : ℝ} (hw : 0 < w) (hw1 : w < 1)
    (hx : x ∈ Ioo (-1 : ℝ) 1) : w^2*x^2 < 1 := by
  have hw2 : w^2 < 1 := by nlinarith
  have hx2 : x^2 < 1 := by nlinarith [hx.1, hx.2, mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)]
  have h : w^2*x^2 ≤ w^2 := by simpa using mul_le_mul_of_nonneg_left hx2.le (sq_nonneg w)
  linarith

theorem linear_parameter_bounds {w x : ℝ} (hw : 0 < w) (hw1 : w < 1)
    (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1-w*x ∧ 0 < 1+w*x := by
  have h₁ := mul_lt_mul_of_pos_left hx.1 hw
  have h₂ := mul_lt_mul_of_pos_left hx.2 hw
  constructor <;> nlinarith

theorem analyticAt_signedLog (c a w x : ℝ) (hc : 0 < c) (hca : c^2-a^2=1)
    (hw : 0 < w) (hw1 : w < 1) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℝ (signedLog c a w) x := by
  by_cases ha : a = 0
  · have hb := linear_parameter_bounds hw hw1 hx
    exact ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).log hb.1).sub
      ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).log hb.2) |>.congr
        (Filter.Eventually.of_forall fun y => by simp [signedLog, ha])
  · have hrpos : 0 < a^2+w^2*x^2 := by
      have := sq_pos_of_ne_zero ha
      nlinarith [mul_nonneg (sq_nonneg w) (sq_nonneg x)]
    have hb := branches_positive c a w (x^2) hc hca hrpos
      (square_parameter_bounds hw hw1 hx)
    have hr : AnalyticAt ℝ (fun y : ℝ => root a w (y^2)) x :=
      AnalyticAt.sqrt_pos (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow 2))) hrpos
    have hlog : AnalyticAt ℝ (fun y : ℝ => logRatio c a w (y^2)) x :=
      ((analyticAt_const.sub hr).div (analyticAt_const.add hr)
        (ne_of_gt hb.2.1)).log hb.2.2.1
    apply hlog.congr
    exact Filter.Eventually.of_forall fun y => by simp [signedLog, ha]

/-- For positive oracle parameters the signed extension agrees with the
logarithm of the paper's actual positive-root ratio. -/
theorem signedLog_eq_logRatio (c a w x : ℝ) (hc : 0 < c) (hca : c^2-a^2=1)
    (hw : 0 < w) (hw1 : w < 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    signedLog c a w x = logRatio c a w (x^2) := by
  by_cases ha : a = 0
  · have hc1 : c = 1 := by rw [ha] at hca; nlinarith
    have hroot : root a w (x^2) = w*x := by
      dsimp [root]
      rw [ha, zero_pow (by norm_num : 2 ≠ 0), zero_add, ← mul_pow,
        Real.sqrt_sq (mul_nonneg hw.le hx.1.le)]
    have hb := linear_parameter_bounds hw hw1 (show x ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith [hx.1,hx.2])
    simp only [signedLog, if_pos ha, logRatio, ratio, minus, plus, hroot, hc1]
    exact (Real.log_div (ne_of_gt hb.1) (ne_of_gt hb.2)).symm
  · simp [signedLog, ha]

/-- The sum at `x` and `-x` keeps exactly the unequal-diagonal term. -/
theorem signedLog_add_neg (c a w x : ℝ) :
    signedLog c a w x + signedLog c a w (-x) =
      if a = 0 then 0 else 2*logRatio c a w (x^2) := by
  by_cases ha : a = 0
  · simp only [signedLog, ha, ↓reduceIte]
    rw [show 1 - w * (-x) = 1 + w*x by ring,
      show 1 + w * (-x) = 1 - w*x by ring]
    ring
  · simp only [signedLog, ha, ↓reduceIte, neg_sq]
    ring

/-- Integer exponents in an identity of actual positive-root ratios become
an identity of the signed analytic logarithmic extensions. -/
theorem continued_log_identity {ι : Type*} (s : Finset ι) (c a w : ι → ℝ) (z : ι → ℤ)
    (hc : ∀ i ∈ s, 0 < c i) (hca : ∀ i ∈ s, c i^2-a i^2=1)
    (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∀ i ∈ s, w i < 1)
    (hid : ∀ x ∈ Ioo (0 : ℝ) 1, ∏ i ∈ s, ratio (c i) (a i) (w i) (x^2) ^ z i = 1) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, ∑ i ∈ s, (z i : ℝ)*signedLog (c i) (a i) (w i) x = 0 := by
  have ha : AnalyticOnNhd ℝ
      (fun x => ∑ i ∈ s, (z i : ℝ)*signedLog (c i) (a i) (w i) x) (Ioo (-1) 1) := by
    intro x hx
    exact s.analyticAt_fun_sum fun i hi => analyticAt_const.mul
      (analyticAt_signedLog _ _ _ _ (hc i hi) (hca i hi) (hw i hi) (hw1 i hi) hx)
  have hz : ∀ x ∈ Ioo (0 : ℝ) 1,
      ∑ i ∈ s, (z i : ℝ)*signedLog (c i) (a i) (w i) x = 0 := by
    intro x hx
    have hp (i : ι) (hi : i ∈ s) : 0 < ratio (c i) (a i) (w i) (x^2) := by
      have hr : 0 < a i^2+w i^2*x^2 := by
        have := mul_pos (sq_pos_of_pos (hw i hi)) (sq_pos_of_pos hx.1)
        nlinarith [sq_nonneg (a i)]
      exact (branches_positive _ _ _ _ (hc i hi) (hca i hi) hr
        (square_parameter_bounds (hw i hi) (hw1 i hi)
          ⟨by linarith [hx.1], hx.2⟩)).2.2.1
    have hlog := congrArg Real.log (hid x hx)
    rw [Real.log_prod _ _ (fun i hi => zpow_ne_zero _ (ne_of_gt (hp i hi))), Real.log_one] at hlog
    simp only [Real.log_zpow] at hlog
    convert hlog using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [signedLog_eq_logRatio _ _ _ _ (hc i hi) (hca i hi) (hw i hi) (hw1 i hi) hx]
    rfl
  apply ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
    (show (1/2 : ℝ) ∈ Ioo (-1) 1 by norm_num)
  filter_upwards [isOpen_Ioo.mem_nhds (show (1/2 : ℝ) ∈ Ioo 0 1 by norm_num)] with x hx
  exact hz x hx

/-- The actual ratio identity imposes a zero logarithmic sum on exactly the
unequal-diagonal classes; equal-diagonal classes are unrestricted. -/
theorem unequal_log_identity {ι : Type*} (s : Finset ι) (c a w : ι → ℝ) (z : ι → ℤ)
    (hc : ∀ i ∈ s, 0 < c i) (hca : ∀ i ∈ s, c i^2-a i^2=1)
    (hw : ∀ i ∈ s, 0 < w i) (hw1 : ∀ i ∈ s, w i < 1)
    (hid : ∀ x ∈ Ioo (0 : ℝ) 1, ∏ i ∈ s, ratio (c i) (a i) (w i) (x^2) ^ z i = 1) :
    ∀ y ∈ Ioo (0 : ℝ) 1,
      ∑ i ∈ s.filter (fun i => a i ≠ 0), (z i : ℝ)*logRatio (c i) (a i) (w i) y = 0 := by
  classical
  intro y hy
  let x := Real.sqrt y
  have hxpos : 0 < x := Real.sqrt_pos.mpr hy.1
  have hxsq : x^2 = y := Real.sq_sqrt hy.1.le
  have hxlt : x < 1 := by nlinarith [hy.2]
  have h₁ := continued_log_identity s c a w z hc hca hw hw1 hid x
    (show x ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith)
  have h₂ := continued_log_identity s c a w z hc hca hw hw1 hid (-x)
    (show -x ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith)
  have hadd : (∑ i ∈ s, (z i : ℝ)*signedLog (c i) (a i) (w i) x) +
      (∑ i ∈ s, (z i : ℝ)*signedLog (c i) (a i) (w i) (-x)) =
      2*(∑ i ∈ s.filter (fun i => a i ≠ 0), (z i : ℝ)*logRatio (c i) (a i) (w i) y) := by
    rw [← Finset.sum_add_distrib, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_add, signedLog_add_neg, hxsq]
    by_cases hai : a i = 0 <;> simp [hai, mul_left_comm, mul_comm]
  rw [h₁, h₂, zero_add] at hadd
  linarith

end PlanarHom.BooleanRatioParity
