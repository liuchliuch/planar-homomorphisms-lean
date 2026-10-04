import PlanarHom.WeightedSpectralField
import PlanarHom.DomainWeightedSpectralAppend
import PlanarHom.FieldPresentationReductions

/-! Inverse-background diagonal availability with exact original domains. The weighted spectral
extension is constructed, and the final answers return to the original basis. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Complexity Complexity.MixedCode FiniteLanguageAliases ProductCompatibility
open SpectralFieldPresentation AlgebraicProductInterpolation PrescribedDomains
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q bt ut dt dimension : ℕ}

def domainInverseDiagonalAppendReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (D : Fin dt→Set (Fin q)) (B : Fin bt→Fin dt→Fin dt→Prop) (T : Fin ut→Fin dt→Prop)
    (old : Fin bt) (full : Fin dt) (hfull : D full=Set.univ)
    (hpath : ∀ x y,B old x y→PathDomainTyping B old full x y) (hA : (realMatrix (M old)).PosDef) (hw : ∀ i,0<(w i : ℝ)) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem b₀ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w D (appendOne B (B old)) T)
      (domainEvaluationProblem b₀ M U w D B T) := by
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
  let first := domainWeightedSpectralAppendReduction bF MF UF wF D B T old full hfull hpath
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
  have second : PromisePolyTimeTuringReduction (domainEvaluationProblem bF MF UF wF D B T)
      (domainEvaluationProblem b₀ M U w D B T) := domainFieldMapReduction b₀ bF φ M U w D B T
  have third := domainFieldDescentReduction b₀ bF φ
    (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹))) U w D (appendOne B (B old)) T
  change PromisePolyTimeTuringReduction
    (domainEvaluationProblem bF (appendOne MF (∑ i,(1 : weightedField A w) • weightedProjector A w i)) UF wF D (appendOne B (B old)) T)
    (domainEvaluationProblem bF MF UF wF D B T) at first
  rw [hsum] at first
  change PromisePolyTimeTuringReduction _ (domainEvaluationProblem bF
    (fun l i j=>φ (appendOne M (Matrix.diagonal (fun i=>(w i)⁻¹)) l i j)) UF wF D (appendOne B (B old)) T) at third
  rw [happ] at third
  exact third.trans (first.trans second)

end PlanarHom.PositiveWeightRemoval
