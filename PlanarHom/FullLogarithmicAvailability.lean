import PlanarHom.FullLogarithmicProductIdentities
import PlanarHom.EffectiveSpectralTransfer
import PlanarHom.UniformMatrixPowerSimulation
import PlanarHom.SpectralRealAvailability

/-!
# Actual full-logarithmic-support reduction to I + J

This is source Lemma 3.11 up to its separately cited Potts-hardness proposition.
The reduction is a genuine raw-word planar polynomial-time oracle machine;
every original binary and unary label remains present. Logarithms are used only
in the proof of the product identities. Queries use positive integer ordinary
matrix powers, implemented by uniform private paths.

No assertion of #P-hardness is made without the external Proposition 2.2(ii).
-/
noncomputable section
namespace PlanarHom.FullLogarithmicAvailability
open Complexity Complexity.MixedCode EffectiveProductTransfer FiniteLanguageAliases
open FullLogarithmicProductIdentities
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q bt ut dimension : ℕ}

omit [FiniteDimensional ℚ K] in
@[simp] theorem pottsMatrix_real (i j : Fin q) :
    ((pottsMatrix : Matrix (Fin q) (Fin q) K) i j : ℝ) =
      (pottsMatrix : Matrix (Fin q) (Fin q) ℝ) i j := by
  by_cases h : i = j
  · simp only [pottsMatrix, if_pos h]
    exact map_ofNat K.val.toRingHom 2
  · simp [pottsMatrix, h]

/-- Positive definiteness supplies the diagonal padding entries. -/
theorem posDef_diagonal_pos {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.PosDef) (i : V) : 0 < A i i := by
  have hx : (Pi.single i (1 : ℝ) : V → ℝ) ≠ 0 := by
    intro hz
    have h := congrFun hz i
    simpa using h
  simpa only [star_trivial, Matrix.mulVec_single_one, single_dotProduct,
    one_mul, Matrix.col_apply] using hA.2 (Pi.single i 1) hx

omit [FiniteDimensional ℚ K] in
/-- Numerical connected support and nonnegativity give the source threshold q-1. -/
theorem power_positive (A : Matrix (Fin q) (Fin q) K)
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix A i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix A) hA.1).Connected)
    (n : ℕ) (hn : q - 1 ≤ n) (i j : Fin q) : 0 < matrixPowerRealFamily A n i j := by
  rw [matrixPowerRealFamily, realPower_nat _ hA.1]
  exact PositivePowers.power_pos_of_connected _ hnonneg (posDef_diagonal_pos _ hA)
    (LogarithmicSupport.offDiagonalSupport _ hA.1)
    (fun {_ j} h => lt_of_le_of_ne (hnonneg _ j) (Ne.symm h.2)) hconn
    (by simpa using hn) i j

omit [FiniteDimensional ℚ K] in
theorem identities (A : Matrix (Fin q) (Fin q) K)
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef)
    (hfull : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix A) i j ≠ 0) :
    ProductIdentities (matrixPowerRealFamily A)
      (fun i j => ((pottsMatrix : Matrix (Fin q) (Fin q) K) i j : ℝ)) := by
  simpa only [pottsMatrix_real] using
    productIdentities (SpectralFieldPresentation.realMatrix A) hA hfull

/-- Source 3.11's actual interpolation reduction. The sign of a nonzero
logarithmic off-diagonal entry is unrestricted. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hq : 3 ≤ q) (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix (M old) i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix (M old)) hA.1).Connected)
    (hfull : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j ≠ 0) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M pottsMatrix) U (fun _ => 1))
      (evaluationProblem basis M U (fun _ => 1)) :=
  spectral_reduction basis M U (M old) pottsMatrix hA pottsMatrix_symm
    (q - 1) (by omega) (power_positive _ hA hnonneg hconn)
    (identities _ hA hfull) (evaluationProblem basis M U (fun _ => 1))
    (UniformMatrixPowerSimulation.reduction basis M U old)

/-- The already supplied source oracle is retained by actual reduction composition. -/
def jointlyAvailable (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hq : 3 ≤ q) (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix (M old) i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix (M old)) hA.1).Connected)
    (hfull : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j ≠ 0)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _ => 1)) base) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M pottsMatrix) U (fun _ => 1)) base :=
  (reduction basis M U old hq hA hnonneg hconn hfull).trans available

end PlanarHom.FullLogarithmicAvailability

namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases FullLogarithmicProductIdentities
variable {q bt ut : ℕ} (L : RealLanguage q bt ut)

/-- The new target lives in the original source number field, without a field extension. -/
def pottsTargetProblem : PromiseProblem :=
  evaluationProblem L.basis (appendOne L.matricesK pottsMatrix) L.unariesK (fun _ => 1)

/-- Source-facing Lemma 3.11 reduction, retaining the given mixed language and base oracle. -/
def lemma311_reduction (hunit : ∀ i, L.weights i = 1) (old : Fin bt)
    (hq : 3 ≤ q) (hA : (L.matrices old).PosDef)
    (hnonneg : ∀ i j, 0 ≤ L.matrices old i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices old) hA.1).Connected)
    (hfull : ∀ i j, i ≠ j → EntropyCompletion.matrixLog (L.matrices old) i j ≠ 0)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction L.pottsTargetProblem base := by
  apply (FullLogarithmicAvailability.reduction L.basis L.matricesK L.unariesK old
    hq hA hnonneg hconn hfull).trans
  simpa only [RealLanguage.problem, weightsK_eq_one L hunit] using available

/-- The real target is literally I_q + J_q. -/
theorem pottsTargetMatrix_real :
    (pottsMatrix : Matrix (Fin q) (Fin q) L.field).map L.field.val =
      1 + Matrix.of (fun _ _ => (1 : ℝ)) := by
  rw [← pottsMatrix_eq_one_add_ones]
  ext i j
  exact FullLogarithmicAvailability.pottsMatrix_real i j

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
