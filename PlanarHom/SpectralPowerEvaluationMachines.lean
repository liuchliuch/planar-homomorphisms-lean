import PlanarHom.FixedFieldPolynomialMachines
import PlanarHom.FixedPowerMachines
import PlanarHom.FixedFieldEncodingTransport
import PlanarHom.SpectralFieldPresentation

/-! Actual unary-integer evaluation of fixed Hermitian algebraic matrix powers.
A single fixed splitting field is used and each entry is returned to the original
fixed source basis through a compiled rational-linear retraction. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.SpectralPowerEvaluationMachines
open Complexity FixedFieldPolynomialMachines
open Complexity.MixedCode
variable {K : Type} [Field K] [Algebra ℚ K] {dimension q s : ℕ}

/-- Fixed spectral sums are compiled from actual fixed-base scalar power machines. -/
theorem fp_spectralEntry (basis : Module.Basis (Fin dimension) ℚ K)
    (a c : Fin s → K) : FP BitEncoding.unaryNat (numberFieldEncoding basis)
      (fun n => ∑ i, a i ^ n * c i) := by
  apply fp_sum basis BitEncoding.unaryNat Finset.univ
  intro i _
  exact (((FixedPowerMachines.fp_power basis (a i)).pair
    (fp_const BitEncoding.unaryNat (numberFieldEncoding basis) (c i))).comp
      (FixedFieldArithmetic.fp_multiplication basis))

variable {L : Type} [Field L] [Algebra ℚ L] {dL : ℕ}

/-- A proved spectral decomposition over one fixed extension supplies an actual
matrix-power evaluator in the original field presentation. -/
theorem fp_matrixPowers_of_spectral_embedding
    (bK : Module.Basis (Fin dimension) ℚ K) (bL : Module.Basis (Fin dL) ℚ L)
    (φ : K →ₐ[ℚ] L) (M : Matrix (Fin q) (Fin q) K)
    (a : Fin s → L) (P : Fin s → Matrix (Fin q) (Fin q) L)
    (hp : ∀ n i j, φ ((M ^ n) i j) = ∑ k, a k ^ n * P k i j) :
    FP BitEncoding.unaryNat ((numberFieldEncoding bK).vector (q * q))
      (fun n => binaryAlphabet (M ^ n)) := by
  obtain ⟨g, hg, hfp⟩ := FixedFieldEncodingTransport.exists_fp_leftInverse bK bL
    φ.toLinearMap φ.injective
  apply FixedVectorMachines.fp_assemble
  intro e
  have h := (fp_spectralEntry bL a
    (fun k => P k (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2)).comp hfp
  exact h.congr (fun n => by
    dsimp only [Function.comp_def]
    rw [← hp]
    exact hg _)

variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]

/-- Source3.10(S)'s matrix powers have polynomial bit complexity in the unary
integer parameter. No runtime spectral oracle or field compositum is assumed. -/
theorem fp_matrixPowers (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Matrix (Fin q) (Fin q) K₀) (hM : (SpectralFieldPresentation.realMatrix M).IsHermitian) :
    FP BitEncoding.unaryNat ((numberFieldEncoding b₀).vector (q * q))
      (fun n => binaryAlphabet (M ^ n)) := by
  let f : ℝ → ℝ := id
  have hf : ∀ x ∈ spectrum ℝ (SpectralFieldPresentation.realMatrix M), IsAlgebraic ℚ (f x) := by
    intro x hx
    exact AlgebraicSpectralData.isAlgebraic_of_mem_spectrum _
      (SpectralFieldPresentation.realMatrix_isAlgebraic M) hx
  let bF := SpectralFieldPresentation.basis M hM f hf
  apply fp_matrixPowers_of_spectral_embedding b₀ bF
    (SpectralFieldPresentation.inclusion M f) M
    (SpectralFieldPresentation.a M f) (SpectralFieldPresentation.P M f)
  intro n i j
  have hm := map_pow (SpectralFieldPresentation.inclusion M f).toRingHom.mapMatrix M n
  have hp := SpectralFieldPresentation.sourceMatrix_pow M hM f n
  have he := congrArg (fun N => N i j) (hm.trans hp)
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul] using he

end PlanarHom.SpectralPowerEvaluationMachines
