import PlanarHom.ClockSmallCharts
import PlanarHom.InjectiveWeightedStructuralTransfer

noncomputable section
open Classical
namespace PlanarHom.ClockModel
open Structures Boolean

theorem weighted_class_sufficient {q:ℕ} {K:ℝ} (hK:K≠0)
    (w:Fin q→ℝ) (hq:q=2 ∨ q=4) (μ:ℝ) (hμ:0 < μ) (hw:∀i,w i=μ) :
    PositiveVertexWeightClass (interaction q K) w (symmetric q K) := by
  apply actual_membership_of_weightedClass _ _ _ (rows_injective hK)
  rcases hq with rfl|rfl
  · apply AllowedWeightedBlock.weightedClass
    exact CenteredLogStructural.scaled_tensor_allowedBlock (interaction 2 K) w twoChart
      (Real.exp K) μ (Real.exp_pos K) hμ (fun _:Fin 1=>Real.exp (-2*K))
      (fun _=>⟨Real.exp_pos _,exp_parameter_nonunit hK (-2) (by norm_num)⟩) (two_tensor K) hw
  · apply AllowedWeightedBlock.weightedClass
    exact CenteredLogStructural.scaled_tensor_allowedBlock (interaction 4 K) w fourChart
      (Real.exp K) μ (Real.exp_pos K) hμ (fun _:Fin 2=>Real.exp (-K))
      (fun _=>⟨Real.exp_pos _,by simpa using exp_parameter_nonunit hK (-1) (by norm_num)⟩)
      (four_tensor K) hw

theorem weighted_class_iff {q:ℕ} (hq:2≤q) {K:ℝ} (hK:K≠0)
    (w:Fin q→ℝ) (hw:∀i,0 < w i) :
    PositiveVertexWeightClass (interaction q K) w (symmetric q K) ↔
      (q=2 ∨ q=4) ∧ ∃μ:ℝ,0 < μ ∧ ∀i,w i=μ :=
  ⟨weighted_class_necessary hq hK w hw,fun ⟨h,μ,hμ,hw⟩=>weighted_class_sufficient hK w h μ hμ hw⟩

end PlanarHom.ClockModel
