import PlanarHom.DistanceKernelAvailability
import PlanarHom.SpectralRealAvailability

/-! Real-algebraic source-facing uniform distance-kernel availability. Original
language, output presentation, old constraints and the supplied base oracle are
retained; the new parameter is the actual rational x. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode LogarithmicSupport
variable {q bt ut : ℕ} (L : RealLanguage q bt ut)

def distanceKernelTargetProblem (old : Fin bt) : PromiseProblem :=
  ParameterizedMatrixEvaluation.problem L.basis BitEncoding.rat L.matricesK L.unariesK (fun _ => 1)
    (DistanceKernelEvaluationMachines.matrix (DistanceKernelAvailability.graph (L.matricesK old)))
    (fun x : ℚ => 0 < x)

/-- The algebraic source presentation induces literally the original real log graph. -/
theorem distanceKernelGraph_eq (old : Fin bt) :
    DistanceKernelAvailability.graph (L.matricesK old) = logSupport (L.matrices old) := rfl

/-- Source4.2's uniform computation, including arbitrary fixed coexisting labels. -/
def lemma42_uniform (hunit : ∀ i, L.weights i=1) (old : Fin bt)
    (hH : (L.matrices old).PosDef) (hconn : (logSupport (L.matrices old)).Connected)
    (hpositive : ∀ i j, (logSupport (L.matrices old)).Adj i j →
      0 < EntropyCompletion.matrixLog (L.matrices old) i j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.distanceKernelTargetProblem old) base := by
  apply (DistanceKernelAvailability.uniformReduction L.basis L.matricesK L.unariesK old
    hH hconn hpositive).trans
  simpa only [RealLanguage.problem, weightsK_eq_one L hunit] using available

/-- The appended matrix is exactly the paper's real distance kernel. -/
theorem distanceKernelTargetMatrix_real (old : Fin bt) (x : ℚ) :
    (DistanceKernelEvaluationMachines.matrix (K := L.field)
      (DistanceKernelAvailability.graph (L.matricesK old)) x).map L.field.val =
      EntropyCompletion.distanceKernel (logSupport (L.matrices old)) (x : ℝ) := by
  ext i j
  exact DistanceKernelEvaluationMachines.matrix_real _ _ _ _

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
