-- Source necessity endpoint extraction; closed complexity endpoints are assembled separately.
/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.RectangularUnweightedSourceFormsConditional
import PlanarHom.BipartiteWeightedSourceCanonical
import PlanarHom.RectangularNormalizedCoreClassificationConditional

/-! Complete source Theorem9.1. The normalized core, original class moments,
independent side charts, and original amplitudes are all derived from actual
source programs. No chart, classification, or availability theorem is supplied. -/
noncomputable section
open Classical
namespace PlanarHom.RectangularUnweightedSourceForms
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open RectangularSourceNormSimulation (block realRectangular)
open RectangularBackgroundSourceNormSimulation (weights)
open BipartiteWeightedSourceCanonical Complexity Complexity.MixedCode
variable {p s n : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]
variable {K₀ : IntermediateField ℚ ℝ}

/-- Literal original finite-field source, with arbitrary repeated and
proportional rows and columns. Its output basis remains unchanged. -/
theorem source_form_of_not_hard_of_potts (hPotts : PositivePottsFoundation) (basis : Module.Basis (Fin n) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (hnot : ¬PromisedSharpPHard
      (evaluationProblem basis (fun _:Fin 1=>block V) (fun u:Fin 0=>u.elim0) (fun _=>1))) :
    RectangularTensorForm (realRectangular V) := by
  obtain ⟨d,eR,eC,γ,ρ,hγ,hρ,hcore⟩ :=
    RectangularNormalizedCoreClassification.source_unit_core_tensor_of_potts hPotts basis V hV hnot
  exact source_form_of_core_of_potts hPotts basis V hV eR eC γ hγ ρ
    (fun r=>⟨(hρ r).1,ne_of_lt (hρ r).2⟩) hcore hnot

/-- Canonical source-language necessity without a normalized-core hypothesis. -/
theorem source_language_form_of_not_hard_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage (p+s) 1 0)
    (V : Matrix (Fin p) (Fin s) ℝ) (hV : ∀ i j,0<V i j)
    (hM : ∀ i j,L.matrices 0 i j=block V i j) (hunit : ∀ i,L.weights i=1)
    (hnot : ¬PromisedSharpPHard L.problem) : RectangularTensorForm V := by
  let A := fieldCross L
  have hAreal : realRectangular A=V := fieldCross_real L V hM
  have hA : ∀ i j,0<(A i j:ℝ) := by
    intro i j
    change 0<realRectangular A i j
    rw [hAreal]
    exact hV i j
  have hw : weights (fieldLeftWeight L) (fieldRightWeight L)=(fun _=>1) := by
    rw [←fieldWeights L]
    funext i
    exact Subtype.ext (hunit i)
  have heq := problem_eq L V hM
  rw [hw] at heq
  have hnotA : ¬PromisedSharpPHard
      (evaluationProblem L.basis (fun _:Fin 1=>block A) (fun u:Fin 0=>u.elim0) (fun _=>1)) := by
    rw [←heq]
    exact hnot
  have hf := source_form_of_not_hard_of_potts hPotts L.basis A hA hnotA
  rwa [hAreal] at hf

end PlanarHom.RectangularUnweightedSourceForms
