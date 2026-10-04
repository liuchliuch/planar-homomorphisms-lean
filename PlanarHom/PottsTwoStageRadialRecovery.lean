import PlanarHom.PottsTwoStageCorrectness
import PlanarHom.PottsRadialValueNormalization

/-! The concrete two-stage machine consumes the exact diagonal-Tutte radial
values of the actual parallel source graphs. The remaining radial graph
coefficient theorem must supply these values from its literal encoded queries. -/
noncomputable section
open Classical
namespace PlanarHom.PottsTwoStageMachines
open Complexity Complexity.MixedCode MultiGraph PottsTwoStageInterpolation

theorem recover_threeState_radialAnswers (g : MixedCode) (hg : g.Valid 1 0)
    [Nonempty (Fin g.vertices)] (δ : ℚ) (hδ : 1<δ) (answers : List ℚ)
    (ha : ∀ k<g.vertices,∀ l<g.edges.length+1,
      answers.getD (k*(g.edges.length+1)+l) 0=
        radialValue ((g.parallelLabel 0 (l+1)).toMultiGraph
          (parallelLabel_valid 0 (l+1) 1 0 g hg)) δ (k+1)) :
    recover δ 3 1 (g.vertices,(g.edges.length,answers))=
      (g.toMultiGraph hg).unweighted (ProperColoringPottsReduction.positivePottsMatrix 3) := by
  have hh := recover_threeState_samples (g.toMultiGraph hg) δ hδ answers
  simp only [Fintype.card_fin] at hh
  apply hh
  intro k hk l hl
  rw [ha k hk l hl,normalize_radialValue_parallel g hg δ (k+1) (l+1)]
  rfl
end PlanarHom.PottsTwoStageMachines
