import PlanarHom.SpectralCFCOverfield
import PlanarHom.AlgebraicProductInterpolation

/-! Source-facing real-algebraic spectral interpolation for Lemma 3.3.
The original unit-background mixed language and supplied availability oracle
are retained. Spectral data, matrix powers, algebraicity and bit algorithms
are derived from PSD/PD hypotheses, not added as endpoint assumptions. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases
open SpectralFieldPresentation SpectralAvailability
variable {q bt ut : ℕ} (L : RealLanguage q bt ut)

/-- The source lemma uses unit background weights, including at new path vertices. -/
theorem weightsK_eq_one (hunit : ∀ i, L.weights i=1) : L.weightsK = fun _ => 1 := by
  funext i
  apply Subtype.ext
  exact hunit i

def rangeTargetProblem (old : Fin bt) (hC : (L.matrices old).PosSemidef) : PromiseProblem :=
  evaluationProblem
    (SpectralFieldPresentation.basis (L.matricesK old) hC.1 rangeFunction (rangeFunction_algebraic _))
    (appendOne (fun l i j => inclusion (L.matricesK old) rangeFunction (L.matricesK l i j))
      (N (L.matricesK old) rangeFunction))
    (fun l i => inclusion (L.matricesK old) rangeFunction (L.unariesK l i)) (fun _ => 1)

def rationalPowerTargetProblem (old : Fin bt) (hC : (L.matrices old).PosDef) (r : ℚ) : PromiseProblem :=
  evaluationProblem
    (SpectralFieldPresentation.basis (L.matricesK old) hC.1 (fun x => x ^ (r : ℝ)) (powerFunction_algebraic (L.matricesK old) hC r))
    (appendOne (fun l i j => inclusion (L.matricesK old) (fun x => x ^ (r : ℝ)) (L.matricesK l i j))
      (N (L.matricesK old) (fun x => x ^ (r : ℝ))))
    (fun l i => inclusion (L.matricesK old) (fun x => x ^ (r : ℝ)) (L.unariesK l i)) (fun _ => 1)

/-- Full ordinary raw-planar joint availability of the orthogonal range projector. -/
def lemma33_range (hunit : ∀ i, L.weights i=1) (old : Fin bt)
    (hC : (L.matrices old).PosSemidef) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.rangeTargetProblem old hC) base := by
  apply (rangeAppendOverfieldReduction L.basis L.matricesK L.unariesK old hC).trans
  simpa only [RealLanguage.problem,weightsK_eq_one L hunit] using available

/-- Full ordinary raw-planar joint availability of every fixed rational power,
including negative exponents, for the actual positive-definite source matrix. -/
def lemma33_rationalPower (hunit : ∀ i, L.weights i=1) (old : Fin bt)
    (hC : (L.matrices old).PosDef) (r : ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.rationalPowerTargetProblem old hC r) base := by
  apply (rationalPowerAppendOverfieldReduction L.basis L.matricesK L.unariesK old hC r).trans
  simpa only [RealLanguage.problem,weightsK_eq_one L hunit] using available

/-- The appended field matrix is literally the paper's real orthogonal projector. -/
theorem rangeTargetMatrix_real (old : Fin bt) :
    (N (L.matricesK old) rangeFunction).map (SpectralFieldPresentation.field (L.matricesK old) rangeFunction).val =
      RealSpectralInterpolation.rangeProjector (L.matrices old) := by
  rw [N_map_real]
  rfl

/-- The appended power is the actual real spectral rational power in the source. -/
theorem rationalPowerTargetMatrix_real (old : Fin bt) (r : ℚ) :
    (N (L.matricesK old) (fun x => x ^ (r : ℝ))).map
      (SpectralFieldPresentation.field (L.matricesK old) (fun x => x ^ (r : ℝ))).val =
      RealSpectralInterpolation.rationalPower (L.matrices old) r := by
  rw [N_map_real]
  rfl

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
