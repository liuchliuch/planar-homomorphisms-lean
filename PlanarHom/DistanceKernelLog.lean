import PlanarHom.MatrixExponentialDistance
noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter Asymptotics
namespace PlanarHom.MatrixLogCoefficients
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The genuine distance kernel approaches the identity at first order. -/
theorem distanceKernel_sub_one_isBigO (G : SimpleGraph V) (hG : G.Connected) :
    (fun t => EntropyCompletion.distanceKernel G t - 1) =O[𝓝 0] (fun t : ℝ => t) := by
  apply matrix_isBigO_of_entries
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using (isBigO_zero (E' := ℝ) (fun t : ℝ => t) (𝓝 0))
  · have hd : 1 ≤ G.dist i j := by
      have hne : G.dist i j ≠ 0 := fun h => hij (hG.dist_eq_zero_iff.mp h)
      omega
    have h := pow_isBigO_pow hd
    simpa only [EntropyCompletion.distanceKernel, Matrix.sub_apply,
      Matrix.one_apply_ne hij, sub_zero, pow_one] using h

/-- Every edge of the distance kernel has logarithmic expansion `t+O(t²)`. -/
theorem matrixLog_distanceKernel_edge_sub_linear_isBigO (G : SimpleGraph V)
    (hG : G.Connected) (i j : V) (hij : G.Adj i j) :
    (fun t => EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel G t) i j - t)
      =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  let Q : ℝ → Matrix V V ℝ := fun t => EntropyCompletion.distanceKernel G t - 1
  have hQ : Q =O[𝓝 0] (fun t : ℝ => t) := distanceKernel_sub_one_isBigO G hG
  have hz : Tendsto Q (𝓝 0) (𝓝 0) := hQ.trans_tendsto tendsto_id
  have hh : ∀ᶠ t in 𝓝 0, (Q t).IsHermitian := Eventually.of_forall fun t =>
    (EntropyCompletion.distanceKernel_isHermitian G t).sub Matrix.isHermitian_one
  have hr := entry_isBigO (matrixLog_sub_logTaylor_isBigO_pow Q hh hz 1 1
    (by simpa using hQ)) i j
  have heq : ∀ t, 1 + Q t = EntropyCompletion.distanceKernel G t := by intro t; dsimp [Q]; abel
  simpa only [logTaylor_one, heq, Q, Matrix.sub_apply, Matrix.one_apply_ne hij.ne,
    sub_zero, EntropyCompletion.distanceKernel_edge G _ hij, Nat.reduceAdd, Nat.one_mul] using hr

/-- Hence every graph edge persists as a positive logarithmic edge near zero. -/
theorem eventually_matrixLog_distanceKernel_edge_pos (G : SimpleGraph V)
    (hG : G.Connected) (i j : V) (hij : G.Adj i j) :
    ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      0 < EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel G t) i j := by
  apply eventually_pos_of_positive_leading (a := 1) zero_lt_one 1
  simpa using matrixLog_distanceKernel_edge_sub_linear_isBigO G hG i j hij

end PlanarHom.MatrixLogCoefficients
