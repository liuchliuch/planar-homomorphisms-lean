import PlanarHom.FisherCubicRowSemantics
import PlanarHom.FisherPipelineValidity

/-! NEW complete realization of the actual numeric two-stage inherited
Fisher row table. Every finite row and occurrence address is identified exactly. -/
noncomputable section
open Classical
namespace PlanarHom.FisherInheritedRowCode
open Complexity MultiGraph Fisher PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)

 def typedInheritedRows : RotationRows ((FisherCodePipeline.code g).toMultiGraph (FisherCodePipeline.valid hg)) :=
  typedCubicRows (FisherCodePipeline.intermediate g) (FisherCodePipeline.intermediate_valid hg)
    (FisherCodePipeline.intermediate_cubic hg)
    (typedExpansionRows g hg (FisherContourOrder.ordering g hg) (FisherContourOrder.computed_realizes g hg))

 theorem inheritedRows_realizes : PlanarityRowFaceCode.Realizes (FisherCodePipeline.code g)
    (FisherCodePipeline.valid hg) (inheritedRows g) (typedInheritedRows g hg) :=
  cubicRows_realizes (FisherCodePipeline.intermediate g) (FisherCodePipeline.intermediate_valid hg)
    (FisherCodePipeline.intermediate_cubic hg) (expansionRows g)
    (typedExpansionRows g hg (FisherContourOrder.ordering g hg) (FisherContourOrder.computed_realizes g hg))
    (expansionRows_realizes g hg)

end PlanarHom.FisherInheritedRowCode
