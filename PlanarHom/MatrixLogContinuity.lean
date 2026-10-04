import PlanarHom.MatrixLogCoefficients
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuity of the spectral matrix logarithm near the identity

Uniform convergence of the explicitly controlled Taylor polynomials gives
continuity on the Hermitian half-ball. The logarithm throughout is the genuine
continuous-functional-calculus logarithm from `EntropyCompletion`.
-/

noncomputable section
open scoped NNReal BigOperators Matrix.Norms.Operator Topology
open Filter

namespace PlanarHom.MatrixLogContinuity

open MatrixLogCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [Nonempty V] in
/-- Each truncation of the matrix logarithm series is a continuous polynomial. -/
theorem continuous_logTaylor (n : ℕ) :
    Continuous (fun Q : Matrix V V ℝ => logTaylor Q n) := by
  unfold logTaylor
  fun_prop

/-- Uniform convergence to the actual spectral logarithm on the Hermitian half-ball. -/
theorem tendstoUniformlyOn_logTaylor :
    TendstoUniformlyOn (fun n (Q : Matrix V V ℝ) => logTaylor Q n)
      (fun Q => EntropyCompletion.matrixLog (1 + Q)) atTop
      {Q | Q.IsHermitian ∧ ‖Q‖ ≤ 1 / 2} := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun n : ℕ =>
      (2 * (Fintype.card V : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, mul_zero, zero_mul] using
      tendsto_const_nhds.mul (hp.mul tendsto_const_nhds)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb.eventually_lt_const hε] with n hn Q hQ
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (norm_matrixLog_sub_logTaylor_le_half Q hQ.1 hQ.2 n)
  apply lt_of_le_of_lt _ hn
  gcongr
  exact hQ.2

/-- The spectral logarithm is continuous on Hermitian perturbations of norm at most one half. -/
theorem continuousOn_matrixLog_one_add :
    ContinuousOn (fun Q : Matrix V V ℝ => EntropyCompletion.matrixLog (1 + Q))
      {Q | Q.IsHermitian ∧ ‖Q‖ ≤ 1 / 2} :=
  tendstoUniformlyOn_logTaylor.continuousOn
    (Filter.Eventually.of_forall fun n => (continuous_logTaylor n).continuousOn)

/-- Composition along any continuous Hermitian curve contained in the half-ball. -/
theorem continuousOn_matrixLog_one_add_comp {α : Type*} [TopologicalSpace α]
    (Q : α → Matrix V V ℝ) {s : Set α} (hcont : ContinuousOn Q s)
    (hherm : ∀ t ∈ s, (Q t).IsHermitian) (hsmall : ∀ t ∈ s, ‖Q t‖ ≤ 1 / 2) :
    ContinuousOn (fun t => EntropyCompletion.matrixLog (1 + Q t)) s := by
  exact continuousOn_matrixLog_one_add.comp hcont (fun t ht => ⟨hherm t ht, hsmall t ht⟩)

/-- A continuous Hermitian perturbation vanishing at zero has a continuous
spectral logarithm on a genuine open interval about zero. -/
theorem exists_pos_continuousOn_matrixLog_one_add_comp
    (Q : ℝ → Matrix V V ℝ) (hcont : Continuous Q)
    (hherm : ∀ t, (Q t).IsHermitian) (hzero : Q 0 = 0) :
    ∃ δ > 0, ContinuousOn (fun t => EntropyCompletion.matrixLog (1 + Q t))
      (Set.Ioo (-δ) δ) := by
  have hlim : Tendsto Q (𝓝 0) (𝓝 0) := by
    simpa only [hzero] using hcont.continuousAt.tendsto (x := 0)
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), ‖Q t‖ < 1 / 2 := by
    apply Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
    simpa using hlim.norm
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨δ, hδ, continuousOn_matrixLog_one_add_comp Q hcont.continuousOn
    (fun t _ => hherm t) ?_⟩
  intro t ht
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    change dist t 0 < δ
    simpa only [Real.dist_eq, sub_zero, abs_lt] using ht
  exact (hball htball).le

/-- The graph-distance kernel has a continuous spectral logarithm near zero. -/
theorem exists_pos_continuousOn_matrixLog_distanceKernel
    (G : SimpleGraph V) (hG : G.Connected) :
    ∃ δ > 0, ContinuousOn
      (fun t => EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel G t))
      (Set.Ioo (-δ) δ) := by
  obtain ⟨δ, hδ, hc⟩ := exists_pos_continuousOn_matrixLog_one_add_comp
    (fun t => EntropyCompletion.distanceKernel G t - 1)
    ((EntropyCompletion.continuous_distanceKernel G).sub continuous_const)
    (fun t => (EntropyCompletion.distanceKernel_isHermitian G t).sub Matrix.isHermitian_one)
    (by simp only [EntropyCompletion.distanceKernel_zero G hG, sub_self])
  refine ⟨δ, hδ, ?_⟩
  have hcancel (t : ℝ) :
      1 + (EntropyCompletion.distanceKernel G t - 1) =
        EntropyCompletion.distanceKernel G t := by abel
  simpa only [hcancel] using hc

end PlanarHom.MatrixLogContinuity
