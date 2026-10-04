import PlanarHom.EffectiveSpectralTransfer
import PlanarHom.ParameterizedMatrixFamilyReduction

/-! Uniform target-parameter transfer over one fixed number field, the constant
field special case of Lemma3.10(a)–(c). Varying extension-field presentations are
not covered by these endpoints. -/
noncomputable section
namespace PlanarHom.EffectiveProductTransfer
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {X : Type} {q bt ut dimension : ℕ}

/-- Polynomial source, runtime target, one prescribed fixed field and basis. -/
def polynomial_parameter_reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ex : BitEncoding X) (allowed : X → Prop)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (F : Matrix (Fin q) (Fin q) (Polynomial K)) (B : X → Matrix (Fin q) (Fin q) K)
    (d n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hdegree : ∀ i j, (F i j).natDegree ≤ d)
    (hFsym : ∀ x i j, polynomialRealFamily F x i j = polynomialRealFamily F x j i)
    (hBsym : ∀ x, allowed x → ∀ i j, B x i j = B x j i)
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x)))
    (hpositive : ∀ n, n₀ ≤ n → ∀ i j, 0 < polynomialRealFamily F n i j)
    (hidentity : ∀ x, allowed x → ProductIdentities (polynomialRealFamily F)
      (fun i j => (B x i j : ℝ)))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (DynamicMatrixFamilySource.problem basis M U (fun _ => 1) (polynomialFamily F)) base) :
    PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex M U (fun _ => 1) B allowed) base := by
  apply ParameterizedMatrixFamilyReduction.reduction basis ex M U (fun _ => 1)
    (polynomialFamily F) B allowed n₀ hn₀ (polynomialCandidateCount q d)
  · exact FixedFieldPolynomialMachines.fp_polynomialFamily basis
      (fun e : Fin (q*q) => F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2)
  · exact hB
  · intro n hn i j hz
    have hp := hpositive n hn i j
    rw [← polynomialFamily_coe, hz] at hp
    exact lt_irrefl 0 hp
  · intro x hx
    exact polynomial_samples F (B x) d n₀ hdegree hFsym (hBsym x hx) (hidentity x hx)
  · exact simulation

/-- Spectral source, runtime target, actual fixed splitting-field evaluator with
answers returned in the original field. Source and target parameters are separate. -/
def spectral_parameter_reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (ex : BitEncoding X) (allowed : X → Prop)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (A : Matrix (Fin q) (Fin q) K) (B : X → Matrix (Fin q) (Fin q) K)
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef)
    (hBsym : ∀ x, allowed x → ∀ i j, B x i j = B x j i)
    (hB : FP ex ((numberFieldEncoding basis).vector (q*q)) (fun x => binaryAlphabet (B x)))
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀)
    (hpositive : ∀ n, n₀ ≤ n → ∀ i j, 0 < matrixPowerRealFamily A n i j)
    (hidentity : ∀ x, allowed x → ProductIdentities (matrixPowerRealFamily A)
      (fun i j => (B x i j : ℝ)))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (DynamicMatrixFamilySource.problem basis M U (fun _ => 1) (fun n => A ^ n)) base) :
    PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex M U (fun _ => 1) B allowed) base := by
  apply ParameterizedMatrixFamilyReduction.reduction basis ex M U (fun _ => 1)
    (fun n => A ^ n) B allowed n₀ hn₀
    (spectralCandidateCount q (Nat.card (spectrum ℝ (SpectralFieldPresentation.realMatrix A))))
  · exact SpectralPowerEvaluationMachines.fp_matrixPowers basis A hA.1
  · exact hB
  · intro n hn i j hz
    have hp := hpositive n hn i j
    rw [← matrixPowerFamily_coe A hA.1, hz] at hp
    exact lt_irrefl 0 hp
  · intro x hx
    exact spectral_samples A (B x) hA n₀ (hBsym x hx) (hidentity x hx)
  · exact simulation

end PlanarHom.EffectiveProductTransfer
