import PlanarHom.ColoringFramedMacroFamily
import PlanarHom.ColoringFramedCyclicPorts

noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedMacro
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles PositiveBlockProgram
 theorem ports_cyclic (s : CellShape) : CyclicSublist (rows s).facePerm
    ((List.ofFn (fun i=>reversePerm _ (leftClosing s i))).reverse++
      List.ofFn (fun i=>reversePerm _ (rightClosing s i))) := by
  cases s with
  | wireTop => exact ColoringMacroFaces.WireFramed.typed_ports_cyclic
  | wireBottom => exact ColoringMacroFaces.WireFramed.typed_ports_cyclic
  | wireDown => exact ColoringMacroFaces.WireFramed.typed_ports_cyclic
  | cross => exact ColoringMacroFaces.CrossFramed.typed_ports_cyclic
  | fan => exact ColoringMacroFaces.FanFramed.typed_ports_cyclic
  | test => exact ColoringMacroFaces.TestFramed.typed_ports_cyclic
end PlanarHom.ColoringEmitter.FramedMacro
