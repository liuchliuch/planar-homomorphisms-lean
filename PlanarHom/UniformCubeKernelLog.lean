import PlanarHom.CubeGraphMetric
import PlanarHom.CubeBCHRigidity
import PlanarHom.CubeLocalBlocks
import PlanarHom.DistanceKernelLog
import PlanarHom.WheatstoneSupport
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# A rational uniform cube kernel with a positive direction-local logarithm

No explicit logarithm formula is assumed. The two-color log commutes with the
flip operator, so its diagonal is constant. Actual near-zero edge asymptotics
give a positive off-diagonal entry at a rational parameter. Genuine tensor
exponentiation and log/exp inversion lift it to every Boolean cube.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator Topology
open Filter
namespace PlanarHom.UniformCubeKernelLog
open Boolean

/-- W as an ordinary matrix, with matrix rather than pointwise multiplication. -/
def interaction (x : ℝ) : Matrix Bool Bool ℝ := W x

/-- The two-color coordinate flip. -/
def boolFlip : Matrix Bool Bool ℝ := fun x y => if x = y then 0 else 1

theorem W_isHermitian (x : ℝ) : (interaction x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp [interaction, W, eq_comm]

/-- The two-state interaction commutes with color exchange. -/
theorem W_commute_flip (x : ℝ) : Commute (interaction x) boolFlip := by
  change interaction x * boolFlip = boolFlip * interaction x
  ext a b
  cases a <;> cases b <;> simp [Matrix.mul_apply, interaction, W, boolFlip]

/-- Its genuine spectral logarithm has equal diagonal entries. -/
theorem matrixLog_W_diag_eq (x : ℝ) :
    EntropyCompletion.matrixLog (interaction x) false false = EntropyCompletion.matrixLog (interaction x) true true := by
  have hsa : IsSelfAdjoint (interaction x) := W_isHermitian x
  have hc := hsa.commute_cfc (W_commute_flip x) Real.log
  have he := congrArg (fun A : Matrix Bool Bool ℝ => A false true) hc.eq
  simpa [Matrix.mul_apply, Fintype.sum_bool, boolFlip, EntropyCompletion.matrixLog] using he

/-- The exact two-color logarithm is a scalar identity plus one flip. -/
theorem matrixLog_W_eq (x : ℝ) :
    EntropyCompletion.matrixLog (interaction x) =
      EntropyCompletion.matrixLog (interaction x) false false • (1 : Matrix Bool Bool ℝ) +
      EntropyCompletion.matrixLog (interaction x) false true • boolFlip := by
  have hd := matrixLog_W_diag_eq x
  have hh : (EntropyCompletion.matrixLog (interaction x)).IsHermitian := IsSelfAdjoint.log
  have hs : EntropyCompletion.matrixLog (interaction x) true false = EntropyCompletion.matrixLog (interaction x) false true := by
    simpa only [star_trivial] using hh.apply false true
  ext a b
  cases a <;> cases b <;> simp [boolFlip, hd, hs]

/-- The two-vertex complete-graph distance kernel is exactly W. -/
theorem completeBool_distanceKernel (x : ℝ) :
    EntropyCompletion.distanceKernel (⊤ : SimpleGraph Bool) x = interaction x := by
  ext a b
  by_cases h : a = b <;>
    simp [EntropyCompletion.distanceKernel, SimpleGraph.dist, SimpleGraph.edist_top, interaction, W, h]

/-- There is a positive rational parameter below one whose two-color log has
positive off-diagonal entry and whose actual interaction is positive definite. -/
theorem exists_rat_positive_logW :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < 1 ∧ (interaction (q : ℝ)).PosDef ∧
      0 < EntropyCompletion.matrixLog (interaction (q : ℝ)) false true := by
  have hc : (⊤ : SimpleGraph Bool).Connected := SimpleGraph.connected_top_iff.mpr inferInstance
  have hp : ∀ᶠ x in 𝓝[Set.Ioi 0] 0, (interaction x).PosDef := by
    simpa only [completeBool_distanceKernel] using
      (EntropyCompletion.eventually_posDef_distanceKernel (⊤ : SimpleGraph Bool) hc).filter_mono
        (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hl : ∀ᶠ x in 𝓝[Set.Ioi 0] 0, 0 < EntropyCompletion.matrixLog (interaction x) false true := by
    simpa only [completeBool_distanceKernel] using
      MatrixLogCoefficients.eventually_matrixLog_distanceKernel_edge_pos
        (⊤ : SimpleGraph Bool) hc false true (by simp)
  exact WheatstoneCoefficients.exists_positive_rat_of_eventually (hp.and hl) zero_lt_one

/-- The uniform local logarithm lifts to a scalar identity and the same flip
coefficient in each cube direction. -/
theorem sum_coordinateLift_logW (d : ℕ) (x : ℝ) :
    (∑ r : Fin d, CubeTensorExponential.coordinateLift r (EntropyCompletion.matrixLog (interaction x))) =
      ((d : ℝ) * EntropyCompletion.matrixLog (interaction x) false false) • 1 +
        ∑ r : Fin d, EntropyCompletion.matrixLog (interaction x) false true • bitFlipMatrix r := by
  have hX : boolFlip = CubeTensorExponential.localBlock 0 1 := by
    ext a b
    cases a <;> cases b <;> simp [boolFlip, CubeTensorExponential.localBlock]
  have hterm (r : Fin d) : CubeTensorExponential.coordinateLift r
      (EntropyCompletion.matrixLog (interaction x)) =
      EntropyCompletion.matrixLog (interaction x) false false • 1 +
      EntropyCompletion.matrixLog (interaction x) false true • bitFlipMatrix r := by
    conv_lhs => rw [matrixLog_W_eq]
    rw [CubeTensorExponential.coordinateLift_add, CubeTensorExponential.coordinateLift_smul,
      CubeTensorExponential.coordinateLift_one, CubeTensorExponential.coordinateLift_smul, hX,
      CubeTensorExponential.coordinateLift_localBlock]
    simp
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul]
  simp [nsmul_eq_mul]

/-- The actual cube distance-kernel logarithm is a uniform direction operator. -/
theorem matrixLog_cubeKernel_eq {d : ℕ} (x : ℝ) (hW : (interaction x).PosDef) :
    EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel (cubeGraph d) x) =
      ((d : ℝ) * EntropyCompletion.matrixLog (interaction x) false false) • 1 +
        ∑ r : Fin d, EntropyCompletion.matrixLog (interaction x) false true • bitFlipMatrix r := by
  let S : Matrix (Cube d) (Cube d) ℝ :=
    ∑ r : Fin d, CubeTensorExponential.coordinateLift r (EntropyCompletion.matrixLog (interaction x))
  have he : NormedSpace.exp ℝ S = EntropyCompletion.distanceKernel (cubeGraph d) x := by
    dsimp only [S]
    rw [CubeTensorExponential.exp_sum_coordinateLift_eq_tensor, cubeGraph_distanceKernel_eq_tensor]
    simp only [KernelContinuation.exp_matrixLog hW]
    rfl
  have hS : S.IsHermitian := by
    dsimp only [S]
    rw [sum_coordinateLift_logW]
    exact scalar_add_directions_isHermitian _ _
  rw [← he, ExponentialDual.matrixLog_exp hS]
  exact sum_coordinateLift_logW d x

/-- A positive rational cube kernel supplies the uniform positive coefficient
needed in the cubic commutator argument, in the fixed Boolean coordinates. -/
theorem exists_rat_uniform_positive_cube_log (d : ℕ) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < 1 ∧ ∃ c b : ℝ, 0 < b ∧
      EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel (cubeGraph d) q) =
        c • 1 + ∑ r : Fin d, b • bitFlipMatrix r := by
  obtain ⟨q, hq, hq1, hpd, hb⟩ := exists_rat_positive_logW
  exact ⟨q, hq, hq1, _, _, hb, matrixLog_cubeKernel_eq (d := d) (q : ℝ) hpd⟩

end PlanarHom.UniformCubeKernelLog
