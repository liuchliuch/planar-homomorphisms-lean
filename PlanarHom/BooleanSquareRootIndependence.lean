import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Independence at distinct real square-root branch points

This module supplies a real-analytic alternative to the complex monodromy
argument in Section 5.1. Its functions use `Real.sqrt`, not formal branch
symbols. An identity on the positive interval extends by the proved analytic
identity theorem to the nearest negative branch point. Multiplying by the
vanishing square root there isolates its coefficient.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace PlanarHom.BooleanSquareRootIndependence

/-- The positive real square root is analytic at every positive argument. -/
theorem analyticAt_sqrt {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have h : AnalyticAt ℝ (fun y : ℝ => Real.exp (Real.log y * (1 / 2))) x :=
    analyticAt_rexp.comp ((analyticAt_log hx).mul analyticAt_const)
  apply h.congr
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]

/-- Analyticity of a genuine square root composed with an analytic function. -/
theorem AnalyticAt.sqrt_pos {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hpos : 0 < f x) :
    AnalyticAt ℝ (fun y => Real.sqrt (f y)) x :=
  (analyticAt_sqrt hpos).comp hf

/-- The kernels arising from logarithmic derivatives after `y = x²`. -/
def kernel (b v y : ℝ) : ℝ := 1 / (Real.sqrt (y + b) * (1 - v * y))

theorem denominator_pos {v y : ℝ} (hv : 0 ≤ v) (hv1 : v < 1) (hy : y < 1) :
    0 < 1 - v * y := by
  have h : v * y ≤ v := by nlinarith
  linarith

theorem analyticAt_kernel {b v y : ℝ} (hb : -b < y)
    (hv : 0 ≤ v) (hv1 : v < 1) (hy : y < 1) :
    AnalyticAt ℝ (kernel b v) y := by
  have hs := AnalyticAt.sqrt_pos (show AnalyticAt ℝ (fun z : ℝ => z + b) y from
    analyticAt_id.add analyticAt_const) (by linarith : 0 < y + b)
  have hd : AnalyticAt ℝ (fun z : ℝ => 1 - v * z) y :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  exact analyticAt_const.div (hs.mul hd)
    (mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))
      (ne_of_gt (denominator_pos hv hv1 hy)))

/-- Vanishing on `(0,1)` extends up to the closest branch point. This invokes
mathlib's proved identity theorem for actual real analytic functions. -/
theorem extend_kernel_identity {ι : Type*} (s : Finset ι) (b v q : ι → ℝ)
    {B : ℝ} (hB : 0 < B) (hb : ∀ i ∈ s, B ≤ b i)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hv1 : ∀ i ∈ s, v i < 1)
    (hzero : ∀ y ∈ Ioo (0 : ℝ) 1, ∑ i ∈ s, q i * kernel (b i) (v i) y = 0) :
    ∀ y ∈ Ioo (-B) 1, ∑ i ∈ s, q i * kernel (b i) (v i) y = 0 := by
  have ha : AnalyticOnNhd ℝ (fun y => ∑ i ∈ s, q i * kernel (b i) (v i) y)
      (Ioo (-B) 1) := by
    intro y hy
    exact s.analyticAt_fun_sum fun i hi => analyticAt_const.mul
      (analyticAt_kernel (by have := hb i hi; linarith [hy.1]) (hv i hi) (hv1 i hi) hy.2)
  have he : (fun y => ∑ i ∈ s, q i * kernel (b i) (v i) y) =ᶠ[𝓝 (1 / 2 : ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)] with y hy
    exact hzero y hy
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_Ioo (-B) 1).isPreconnected
    (show (1 / 2 : ℝ) ∈ Ioo (-B) 1 by constructor <;> linarith) he

/-- At the unique leftmost square-root singularity, the coefficient must
vanish. All continuation and limiting operations are on actual real functions. -/
theorem coefficient_at_minimum_eq_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b v q : ι → ℝ) {g : ι} (hg : g ∈ s)
    (hb : 0 < b g) (hmin : ∀ i ∈ s.erase g, b g < b i)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hv1 : ∀ i ∈ s, v i < 1)
    (hzero : ∀ y ∈ Ioo (0 : ℝ) 1, ∑ i ∈ s, q i * kernel (b i) (v i) y = 0) :
    q g = 0 := by
  have hbmin : ∀ i ∈ s, b g ≤ b i := by
    intro i hi
    by_cases h : i = g
    · simp [h]
    · exact (hmin i (Finset.mem_erase.mpr ⟨h, hi⟩)).le
  have hext := extend_kernel_identity s b v q hb hbmin hv hv1 hzero
  let H : ℝ → ℝ := fun y => q g / (1 - v g * y) +
    ∑ i ∈ s.erase g, q i * Real.sqrt (y + b g) /
      (Real.sqrt (y + b i) * (1 - v i * y))
  have hden (i : ι) (hi : i ∈ s) : 1 - v i * (-b g) ≠ 0 :=
    ne_of_gt (denominator_pos (hv i hi) (hv1 i hi) (by linarith))
  have hcont : ContinuousAt H (-b g) := by
    apply ContinuousAt.add
    · exact continuousAt_const.div (continuousAt_const.sub
        (continuousAt_const.mul continuousAt_id)) (hden g hg)
    · apply tendsto_finset_sum
      intro i hi
      have his := Finset.mem_of_mem_erase hi
      have hsq : Real.sqrt (-b g + b i) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (by linarith [hmin i hi]))
      exact (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
        (continuousAt_id.add continuousAt_const))).div
        ((Real.continuous_sqrt.continuousAt.comp
          (continuousAt_id.add continuousAt_const)).mul
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)))
        (mul_ne_zero hsq (hden i his))
  have hH : ∀ y ∈ Ioo (-b g) 1, H y = 0 := by
    intro y hy
    have hsq : Real.sqrt (y + b g) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by linarith [hy.1]))
    have hid : H y = Real.sqrt (y + b g) *
        (∑ i ∈ s, q i * kernel (b i) (v i) y) := by
      rw [← Finset.add_sum_erase s (fun i => q i * kernel (b i) (v i) y) hg]
      simp only [H, mul_add, Finset.mul_sum]
      congr 1
      · dsimp [kernel]
        field_simp
      · apply Finset.sum_congr rfl
        intro i hi
        dsimp [kernel]
        ring
    rw [hid, hext y hy, mul_zero]
  have hev : H =ᶠ[𝓝[>] (-b g)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show -b g < (1 : ℝ) by linarith)] with y hy
    exact hH y hy
  have hlim : H (-b g) = 0 :=
    tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev.symm)
  have hvalue : H (-b g) = q g / (1 - v g * (-b g)) := by
    simp [H]
  rw [hvalue] at hlim
  exact (div_eq_zero_iff).mp hlim |>.resolve_right (hden g hg)

/-- The distinct genuine square-root kernels are linearly independent over
constant real coefficients on `(0,1)`. This is the analytic branch-point step
needed for the unequal-diagonal classes in Section 5.1. -/
theorem kernel_linearIndependent {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b v q : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) (hinj : Set.InjOn b (↑s : Set ι))
    (hv : ∀ i ∈ s, 0 ≤ v i) (hv1 : ∀ i ∈ s, v i < 1)
    (hzero : ∀ y ∈ Ioo (0 : ℝ) 1, ∑ i ∈ s, q i * kernel (b i) (v i) y = 0) :
    ∀ i ∈ s, q i = 0 := by
  intro i hi
  by_contra hqi
  let S := s.filter (fun j => q j ≠ 0)
  have hS : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hqi⟩⟩
  obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image S b hS
  have hgS := (Finset.mem_filter.mp hg).1
  have hqg := (Finset.mem_filter.mp hg).2
  have hsub : S ⊆ s := Finset.filter_subset _ _
  have hzS : ∀ y ∈ Ioo (0 : ℝ) 1, ∑ j ∈ S, q j * kernel (b j) (v j) y = 0 := by
    intro y hy
    rw [← hzero y hy]
    apply Finset.sum_subset hsub
    intro j hj hn
    have hq : q j = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hj, h⟩)
    simp [hq]
  apply hqg
  apply coefficient_at_minimum_eq_zero S b v q hg (hb g hgS) ?_
    (fun j hj => hv j (hsub hj)) (fun j hj => hv1 j (hsub hj)) hzS
  intro j hj
  have hjS := Finset.mem_of_mem_erase hj
  apply lt_of_le_of_ne (hmin j hjS)
  intro heq
  have hgj := hinj hgS (hsub hjS) heq
  exact (Finset.ne_of_mem_erase hj) hgj.symm

end PlanarHom.BooleanSquareRootIndependence
