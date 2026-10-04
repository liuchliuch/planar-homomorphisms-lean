import PlanarHom.FisherInheritedRowSemantics
import PlanarHom.FisherInheritedRowMachines
import PlanarHom.FisherNumericInheritedEuler
import PlanarHom.PlanarityRowPfaffianOrientation

/-! NEW ordinary-input orientation correctness for the actual inherited Fisher
row/face compiler. Source planarity supplies the proved finite component Euler
identity; the runtime program receives no geometric or rotation witness. -/
noncomputable section
open Classical
namespace PlanarHom.FisherInheritedRowCode
open Complexity MultiGraph MultiGraph.Kasteleyn
variable {g : MixedCode} {bt ut : ℕ}

 theorem orientationLog_isPfaffian (hp : g.PlanarValid bt ut) :
    ((FisherCodePipeline.code g).toMultiGraph (FisherCodePipeline.valid hp.1)).IsPfaffianOrientation
      (fun e=>logOrientation (orientationLog g) e.val) :=
  PlanarityRowFaceCode.orientationLog_isPfaffian (FisherCodePipeline.code g) (FisherCodePipeline.valid hp.1)
    (inheritedRows g) (typedInheritedRows g hp.1) (inheritedRows_realizes g hp.1) (componentEuler hp)

end PlanarHom.FisherInheritedRowCode
