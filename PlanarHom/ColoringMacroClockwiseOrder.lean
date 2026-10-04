import PlanarHom.ColoringMacroClockwise
import PlanarHom.ColoringMacroClockwiseTransport

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram PlanarityLRRealization
open RadialPottsAssemblyGeometry

/-- Literal rows are clockwise for the actual six affine macro shapes after
the single prescribed global shear. All finite comparisons are kernel checked. -/
theorem localRows_clockwise (s : CellShape) (v : LocalPatch.Port s ⊕ LocalPatch.Private s) :
    ((MacroRows.localRows s).row v).Pairwise (fun a b=>ClockwiseRayOrder (ray s a) (ray s b)) :=
  localRows_clockwise_of s (clockwise_all s) v

end PlanarHom.ColoringEmitter.MacroGeometry
