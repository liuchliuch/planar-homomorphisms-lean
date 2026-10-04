import PlanarHom.AvailablePositiveBooleanTensor
import PlanarHom.BooleanTensorHardness

/-! NEW closure of the original common-chart Boolean consequences. The biased
hardness premise is discharged by its actual compiler. The separate all-size
Potts constructor for the chart remains in AvailableClosedFamilyCube. -/
noncomputable section
open Classical
namespace PlanarHom.ClosedMatrixFamily.CommonCubeChart
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
variable {q:ℕ} {S:Set (Matrix (Fin q) (Fin q) ℝ)}

theorem connected_tensor (W:CommonCubeChart S) (hA:AlgebraicSourceClosed S)
    (htransfer:EffectiveSpectralClosed S) (hgadget:MixedPlanarGadgetClosed S)
    (P:PromiseProblem)
    (havail:∀N,∀hN:N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hnot:¬PromisedSharpPHard P) (N:Matrix (Fin q) (Fin q) ℝ) (hN:Admissible S N):
    ∃γ:ℝ,∃ρ:Fin W.dimension→ℝ,0<γ ∧ IsAlgebraic ℚ γ ∧
      (∀r,0<ρ r ∧ ρ r<1 ∧ IsAlgebraic ℚ (ρ r)) ∧
      Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=γ • Boolean.tensor ρ:=
  W.connected_tensor_of_biased_foundation BiasedPositiveHardness.biasedBooleanFoundation
    hA htransfer hgadget P havail hnot N hN

theorem positive_tensor (W:CommonCubeChart S) (hA:AlgebraicSourceClosed S)
    (htransfer:EffectiveSpectralClosed S) (hgadget:MixedPlanarGadgetClosed S)
    (P:PromiseProblem)
    (havail:∀N,∀hN:N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hnot:¬PromisedSharpPHard P) (N:Matrix (Fin q) (Fin q) ℝ) (hN:N∈S)
    (hpos:∀i j,0<N i j):
    ∃γ:ℝ,∃ρ:Fin W.dimension→ℝ,0<γ ∧ (∀r,0<ρ r) ∧
      Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=γ • Boolean.tensor ρ:=
  W.positive_tensor_of_biased_foundation BiasedPositiveHardness.biasedBooleanFoundation
    hA htransfer hgadget P havail hnot N hN hpos

end PlanarHom.ClosedMatrixFamily.CommonCubeChart
