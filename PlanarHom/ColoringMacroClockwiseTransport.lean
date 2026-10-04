import PlanarHom.ColoringMacroClockwisePredicates
import PlanarHom.ColoringCanvasDartRays

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram PlanarityLRRealization
open RadialPottsAssemblyGeometry

theorem localRows_clockwise_of (s : CellShape) (h : ∀v,ClockwiseRow s v)
    (v : LocalPatch.Port s ⊕ LocalPatch.Private s) :
    ((MacroRows.localRows s).row v).Pairwise (fun a b=>ClockwiseRayOrder (ray s a) (ray s b)) := by
  simp only [MacroRows.localRows,PlanarityLRRealization.RotationRows.transport,List.pairwise_map]
  change ((MacroRows.numericRows s).row (LocalPatch.localVertexParts s v)).Pairwise
    (fun a b=>ClockwiseRayOrder (ray s a) (ray s b))
  apply List.Pairwise.imp _ (h (LocalPatch.localVertexParts s v))
  intro a b hab
  exact ray_clockwise s a b hab

end PlanarHom.ColoringEmitter.MacroGeometry
