import PlanarHom.DependentDomainMatrixFamilyReduction
import PlanarHom.VariableFieldEffectiveTransfer
import PlanarHom.CrossFieldSampleBounds

/-! Source3.10's target-field uniformity with explicit actual presentations and
operators. All height bounds are derived from presentation bits. The fields are
used separately; source interpolation remains in the one original fixed field. -/
noncomputable section
namespace PlanarHom.EffectiveProductTransfer
open Complexity Complexity.MixedCode PrescribedDomains
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {X : Type} {sourceDimension q bt ut dt : ℕ}

variable (sourceBasis : Module.Basis (Fin sourceDimension) ℚ K₀) (ex : BitEncoding X)
variable (fields : PresentedExtensions sourceBasis ex)

def variableDomainTargetProblem (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (policy : Fin (bt+1) → Fin dt → Fin dt → Prop)
    (typing : Fin ut → Fin dt → Prop)
    (B : ∀ x, Matrix (Fin q) (Fin q) (fields.fields x)) : PromiseProblem :=
  DependentDomainMatrixFamilyReduction.targetProblem (fun x => fields.fields x) ex fields.dimension fields.basis
    (fun x => (IntermediateField.inclusion (fields.source_le x)).toRingHom)
    M U (fun _ => 1) D policy typing B (fun _ => True)

/-- Polynomial source with parameter-dependent real number fields. All target
parameters are taken from X; an arbitrary promised subset of rationals can be
encoded as that subtype, without requiring a membership decision algorithm. -/
def polynomial_variable_domain_reduction
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (policy : Fin (bt+1) → Fin dt → Fin dt → Prop)
    (typing : Fin ut → Fin dt → Prop)
    (F : Matrix (Fin q) (Fin q) (Polynomial K₀))
    (B : ∀ x, Matrix (Fin q) (Fin q) (fields.fields x))
    (d n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hdegree : ∀ i j, (F i j).natDegree ≤ d)
    (hFsym : ∀ x i j, polynomialRealFamily F x i j = polynomialRealFamily F x j i)
    (hBsym : ∀ x i j, B x i j = B x j i)
    (hB : FP ex (DependentFieldCodecs.sigma ex
      (fun x => (numberFieldEncoding (fields.basis x)).vector (q*q)))
      (fun x => ⟨x,binaryAlphabet (B x)⟩))
    (hpositive : ∀ n, n₀ ≤ n → ∀ i j, 0 < polynomialRealFamily F n i j)
    (hidentity : ∀ x, ProductIdentities (polynomialRealFamily F) (fun i j => (B x i j : ℝ)))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M (extendedUnaries U D) (fun _ => 1) (polynomialFamily F) (EncodedGraph policy typing)) base) :
    PromisePolyTimeTuringReduction (variableDomainTargetProblem sourceBasis ex fields M U D policy typing B) base := by
  apply DependentDomainMatrixFamilyReduction.reduction (fun x => fields.fields x)
    sourceBasis ex fields.dimension fields.basis
    (fun x => (IntermediateField.inclusion (fields.source_le x)).toRingHom)
    M U (fun _ => 1) D policy typing (polynomialFamily F) B (fun _ => True) n₀ hn₀ (polynomialCandidateCount q d)
    fields.degreeBound fields.degree_le fields.presentation fields.multiplication fields.addition fields.inclusion
  · exact FixedFieldPolynomialMachines.fp_polynomialFamily sourceBasis
      (fun e : Fin (q*q) => F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2)
  · exact hB
  · intro n hn i j hz
    have hp := hpositive n hn i j
    rw [← polynomialFamily_coe, hz] at hp
    exact lt_irrefl 0 hp
  · intro x _
    exact CrossFieldSampleBounds.polynomial_samples F (B x) d n₀ hdegree hFsym (hBsym x) (hidentity x)
  · exact simulation

/-- Spectral source with separately presented bounded-degree target fields.
No target-field inverse, common compositum or hidden height oracle is assumed. -/
def spectral_variable_domain_reduction
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (policy : Fin (bt+1) → Fin dt → Fin dt → Prop)
    (typing : Fin ut → Fin dt → Prop)
    (A : Matrix (Fin q) (Fin q) K₀) (B : ∀ x, Matrix (Fin q) (Fin q) (fields.fields x))
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef) (hBsym : ∀ x i j, B x i j = B x j i)
    (hB : FP ex (DependentFieldCodecs.sigma ex
      (fun x => (numberFieldEncoding (fields.basis x)).vector (q*q)))
      (fun x => ⟨x,binaryAlphabet (B x)⟩))
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀)
    (hpositive : ∀ n, n₀ ≤ n → ∀ i j, 0 < matrixPowerRealFamily A n i j)
    (hidentity : ∀ x, ProductIdentities (matrixPowerRealFamily A) (fun i j => (B x i j : ℝ)))
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M (extendedUnaries U D) (fun _ => 1) (fun n => A ^ n) (EncodedGraph policy typing)) base) :
    PromisePolyTimeTuringReduction (variableDomainTargetProblem sourceBasis ex fields M U D policy typing B) base := by
  apply DependentDomainMatrixFamilyReduction.reduction (fun x => fields.fields x)
    sourceBasis ex fields.dimension fields.basis
    (fun x => (IntermediateField.inclusion (fields.source_le x)).toRingHom)
    M U (fun _ => 1) D policy typing (fun n => A ^ n) B (fun _ => True) n₀ hn₀
    (spectralCandidateCount q (Nat.card (spectrum ℝ (SpectralFieldPresentation.realMatrix A))))
    fields.degreeBound fields.degree_le fields.presentation fields.multiplication fields.addition fields.inclusion
  · exact SpectralPowerEvaluationMachines.fp_matrixPowers sourceBasis A hA.1
  · exact hB
  · intro n hn i j hz
    have hp := hpositive n hn i j
    rw [← matrixPowerFamily_coe A hA.1, hz] at hp
    exact lt_irrefl 0 hp
  · intro x _
    exact CrossFieldSampleBounds.spectral_samples A (B x) hA n₀ (hBsym x) (hidentity x)
  · exact simulation

end PlanarHom.EffectiveProductTransfer
