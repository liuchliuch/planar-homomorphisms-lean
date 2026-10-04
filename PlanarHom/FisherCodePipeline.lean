import PlanarHom.FisherPipelineValidity
import PlanarHom.FisherCubicWeightSemantics
import PlanarHom.FisherReferenceMachines

/-! NEW exact numeric Ising/Fisher pipeline. The original weighted polynomial
identity is transported through the actual serialized occurrence bijections. -/
noncomputable section
open Classical
namespace PlanarHom.FisherCodePipeline
open Complexity MultiGraph FisherCodeMachines
variable {K : Type} [Field K] [Algebra ℚ K]

 theorem matching_identity (φ : K→+*ℝ) {g : MixedCode} {bt ut : ℕ}
    (hg : g.Valid bt ut) (x : List K) :
    ((code g).toMultiGraph (valid hg)).perfectMatchingSum
      (fun e=>φ ((FisherCubicCode.weights (intermediate g)
        (FisherExpansionCode.weights g (FisherContourOrder.computedRows g) x)).getD e.val 0))=
      (4:ℝ)^g.vertices*(g.toMultiGraph hg).evenSubgraphSum (fun e=>φ (x.getD e.val 0)) := by
  exact (FisherCubicCode.matchingSum_weights (intermediate g) (intermediate_valid hg) (intermediate_cubic hg) φ
    (FisherExpansionCode.weights g (FisherContourOrder.computedRows g) x)).trans
      (FisherExpansionCode.evenSubgraphSum_weights g hg (FisherContourOrder.ordering g hg)
        (FisherContourOrder.computed_realizes g hg) φ x)

 theorem isingWeights_get (ρ : K) (g : MixedCode) (e : Fin g.edges.length) :
    (isingWeights ρ g).getD e.val 0=(1-ρ)/(1+ρ) := by
  simp [isingWeights,List.getD_eq_getElem?_getD,e.isLt]

end PlanarHom.FisherCodePipeline

/-! NEW compatibility alias for the unchanged recovered Ising identity's
literal raw edge-item codec; no forest algorithm or semantic claim is added. -/
namespace PlanarHom.PlanarityOrientedForest
abbrev edgeCode := FisherCodeMachines.edgeCode
end PlanarHom.PlanarityOrientedForest
