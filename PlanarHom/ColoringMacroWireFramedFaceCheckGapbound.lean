import PlanarHom.ColoringMacroWireFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem gapBound_b0 : ∀ i : Fin 10, gapValue (0+i.val) < 2646 := by decide +kernel

theorem gapBound : ∀ i : Fin 10, gapValue i.val < 2646 := by
  simpa only [Nat.zero_add] using gapBound_b0

end PlanarHom.ColoringMacroFaces.WireFramed
