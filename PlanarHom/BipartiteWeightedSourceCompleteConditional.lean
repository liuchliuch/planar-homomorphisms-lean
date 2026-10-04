/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.BipartiteWeightedSourceCanonical
import PlanarHom.BipartiteWeightedSourceFormsConditional
import PlanarHom.RectangularNormalizedCoreClassificationConditional

/-! Complete canonical weighted bipartite necessity for main1.3. All original
field/source, normalization, core classification and moments are constructed. -/
noncomputable section
open Classical
namespace PlanarHom.BipartiteWeightedSourceCanonical
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open RectangularSourceNormSimulation (block realRectangular)
open RectangularBackgroundSourceNormSimulation (weights)
open Complexity Complexity.MixedCode Structures
variable {p s : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]

theorem allowedWeighted_of_not_hard_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage (p+s) 1 0)
    (V : Matrix (Fin p) (Fin s) ℝ) (hV : ∀ i j,0<V i j)
    (hM : ∀ i j,L.matrices 0 i j=block V i j)
    (hinj : Function.Injective (L.matrices 0))
    (hw : ∀ i,0<L.weights i) (hnot : ¬PromisedSharpPHard L.problem) :
    AllowedWeightedBlock (L.matrices 0) L.weights := by
  let A := fieldCross L
  let μ := fieldLeftWeight L
  let ν := fieldRightWeight L
  have hA : ∀ i j,0<(A i j:ℝ) := by
    intro i j
    have he := congrFun (congrFun (fieldCross_real L V hM) i) j
    change 0<realRectangular (fieldCross L) i j
    rw [he]
    exact hV i j
  have hμ : ∀ i,0<(μ i:ℝ) := fun i=>hw (Fin.castAdd s i)
  have hν : ∀ j,0<(ν j:ℝ) := fun j=>hw (Fin.natAdd p j)
  have hnotA : ¬PromisedSharpPHard
      (evaluationProblem L.basis (fun _:Fin 1=>block A) (fun u:Fin 0=>u.elim0) (weights μ ν)) := by
    change ¬PromisedSharpPHard
      (evaluationProblem L.basis (fun _:Fin 1=>block (fieldCross L)) (fun u:Fin 0=>u.elim0)
        (weights (fieldLeftWeight L) (fieldRightWeight L)))
    rw [←problem_eq L V hM]
    exact hnot
  obtain ⟨d,eR,eC,γ,ρ,hγ,hρ,hcore⟩ :=
    RectangularNormalizedCoreClassification.source_core_tensor_of_potts hPotts L.basis A hA μ ν hμ hν hnotA
  have hiR : Function.Injective (realRectangular A) := by
    rw [show realRectangular A=V from fieldCross_real L V hM]
    exact cross_rows_injective L V hM hinj
  have hiC : Function.Injective (realRectangular A).transpose := by
    rw [show realRectangular A=V from fieldCross_real L V hM]
    exact cross_columns_injective L V hM hinj
  have hp := BipartiteWeightedSourceForms.source_allowedWeighted_of_core_of_potts hPotts L.basis A hA hiR hiC
    μ ν hμ hν eR eC γ hγ ρ (fun r=>⟨(hρ r).1,ne_of_lt (hρ r).2⟩) hcore hnotA
  have hm : L.matrices 0=block (realRectangular A) := by
    rw [show realRectangular A=V from fieldCross_real L V hM]
    funext i j
    exact hM i j
  have hweights : L.weights=weights (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)) := by
    funext i
    refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;>
      simp [RectangularBackgroundSourceNormSimulation.weights,μ,ν,fieldLeftWeight,fieldRightWeight]
    all_goals rfl
  rw [hm,hweights]
  exact hp

end PlanarHom.BipartiteWeightedSourceCanonical
