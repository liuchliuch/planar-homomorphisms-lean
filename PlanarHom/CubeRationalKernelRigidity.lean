import PlanarHom.CubeSandwichRigidity
import PlanarHom.UniformCubeKernelLog

/-!
# Canonical cube factors using an actual positive rational distance kernel

The uniform outer logarithm is selected from the proved rational cube-kernel
construction. All structural tensor conclusions are then derived from explicit
numerical bounds on the actual rational sandwich and Schur candidates.
Their computational joint availability is still a separate obligation.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.CubeSandwichRigidity
open Boolean LogarithmicSupport SandwichMaximality CubeTensorExponential
variable {d : ℕ}

/-- The fixed-coordinate tensor conclusion with the outer uniform matrix
supplied by a genuine rational cube distance kernel, rather than assumed. -/
theorem canonical_tensor_of_rational_kernel_maximality
    (C N : Matrix (Cube d) (Cube d) ℝ) (hC : C.IsHermitian) (hN : N.PosDef)
    (hCube : offDiagonalSupport C hC = cubeGraph d)
    (hedge : ∀ z w, (offDiagonalSupport C hC).Adj z w → 0 < C z w)
    (hsquare : RationalSquareSandwichEdgeBound C (EntropyCompletion.matrixLog N) hC IsSelfAdjoint.log)
    (hraw : RationalSandwichEdgeBound C (EntropyCompletion.matrixLog N) hC)
    (hschur : RationalSandwichSchurEdgeBound C (EntropyCompletion.matrixLog N) hC)
    (hKernel : ∀ q : ℚ, 0 < q → (q : ℝ) < 1 →
      RationalSandwichEdgeBound
        (EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel (cubeGraph d) q))
        (EntropyCompletion.matrixLog N) IsSelfAdjoint.log)
    (hnonneg : ∀ z w, 0 ≤ N z w)
    (hconn : (offDiagonalSupport N hN.1).Connected)
    (hAlg : ∀ z w, IsAlgebraic ℚ (N z w)) :
    N = N zeroColor zeroColor • CubeTensorExponential.tensor (canonicalFactor N) ∧
      0 < N zeroColor zeroColor ∧
      ∀ r : Fin d, (canonicalFactor N r).PosDef ∧
        (∀ a b, 0 < canonicalFactor N r a b) ∧
        (∀ a b, IsAlgebraic ℚ (canonicalFactor N r a b)) ∧
        canonicalFactor N r false false = 1 := by
  obtain ⟨q, hq, hq1, c, b, hb, heq⟩ :=
    UniformCubeKernelLog.exists_rat_uniform_positive_cube_log d
  have hUeq : EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel (cubeGraph d) q) =
      uniformDirectionMatrix d c b := heq
  have hUniform : RationalSandwichEdgeBound (uniformDirectionMatrix d c b)
      (EntropyCompletion.matrixLog N) (uniformDirectionMatrix_isHermitian d c b) := by
    have htransport : ∀ (A D : Matrix (Cube d) (Cube d) ℝ)
        (hA : A.IsHermitian) (hD : D.IsHermitian), A = D →
        RationalSandwichEdgeBound A (EntropyCompletion.matrixLog N) hA →
        RationalSandwichEdgeBound D (EntropyCompletion.matrixLog N) hD := by
      intro A D hA hD heq
      cases heq
      exact fun h => h
    exact htransport _ _ IsSelfAdjoint.log (uniformDirectionMatrix_isHermitian d c b)
      hUeq (hKernel q hq hq1)
  exact canonical_tensor_of_sandwich_maximality C N hC hN hCube hedge hsquare hraw hschur
    c b hb hUniform hnonneg hconn hAlg

end PlanarHom.CubeSandwichRigidity
