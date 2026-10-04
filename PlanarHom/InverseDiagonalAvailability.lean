import PlanarHom.WeightedSpectralField
import PlanarHom.WeightedSpectralAppendReduction
import PlanarHom.FieldPresentationReductions

/-! Genuine inverse-background diagonal availability. The weighted spectral
extension is constructed, and the final answers return to the original basis. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases ProductCompatibility
open SpectralFieldPresentation AlgebraicProductInterpolation
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dimension : ℕ}

def inverseDiagonalAppendReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (old : Fin bt) (hA : (realMatrix (M old)).PosDef) (hw : ∀ i,0<(w i : ℝ)) :
    PromisePolyTimeTuringReduction
      (evaluationProblem b₀ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w)
      (evaluationProblem b₀ M U w) := by
  let A := M old
  let φ := weightedInclusion A w
  let bF := weightedBasis A hA w hw
  let MF : Fin bt → Matrix (Fin q) (Fin q) (weightedField A w) := fun l i j=>φ (M l i j)
  let UF : Fin ut → Fin q → weightedField A w := fun l i=>φ (U l i)
  let wF : Fin q → weightedField A w := fun i=>φ (w i)
  have hzero : ∀ i,weightedScalar A w i=0 → (1 : weightedField A w)=0 := by
    intro i hi
    have hr : RealSpectralInterpolation.scalar (weightedSpectralMatrix A w) i=0 :=
      congrArg (fun x : weightedField A w => (x : ℝ)) hi
    exact ((ne_of_gt (RealSpectralInterpolation.scalar_pos _
      (weightedConjugate_posDef (realMatrix A) hA (realWeights w) hw) i)) hr).elim
  have hc : Compatible (weightedScalar A w) (fun _=>(1 : weightedField A w)) := by
    intro xs ys _ _ _ _
    simp
  let first := weightedSpectralAppendReduction bF MF UF wF old
    (weightedProjector A w) (weightedScalar A w) (fun _=>1)
    (weighted_field_chain A hA w hw) hzero hc
  have hsum : (∑ i,(1 : weightedField A w) • weightedProjector A w i) =
      (Matrix.diagonal (fun i=>(w i)⁻¹)).map φ := by
    simpa only [one_smul] using weighted_field_projector_sum A hA w hw
  have happ : (fun l i j=>φ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)) l i j)) =
      appendOne MF ((Matrix.diagonal (fun i=>(w i)⁻¹)).map φ) := by
    funext l
    refine Fin.lastCases ?_ (fun k=>?_) l
    · simp only [appendOne_aux]
      rfl
    · change (fun i j=>φ (appendOne M _ (Fin.castAdd 1 k) i j)) =
        appendOne MF _ (Fin.castAdd 1 k)
      simp only [appendOne_old]
      rfl
  have second : PromisePolyTimeTuringReduction (evaluationProblem bF MF UF wF)
      (evaluationProblem b₀ M U w) := fieldMapReduction b₀ bF φ M U w
  have third := fieldDescentReduction b₀ bF φ
    (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w
  change PromisePolyTimeTuringReduction
    (evaluationProblem bF (appendOne MF (∑ i,(1 : weightedField A w) • weightedProjector A w i)) UF wF)
    (evaluationProblem bF MF UF wF) at first
  rw [hsum] at first
  change PromisePolyTimeTuringReduction _ (evaluationProblem bF
    (fun l i j=>φ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)) l i j)) UF wF) at third
  rw [happ] at third
  exact third.trans (first.trans second)

end PlanarHom.PositiveWeightRemoval
