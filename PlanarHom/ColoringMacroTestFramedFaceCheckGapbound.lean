import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem gapBound_b0 : ∀ i : Fin 13, gapValue (0+i.val) < 570 := by decide +kernel

theorem gapBound : ∀ i : Fin 13, gapValue i.val < 570 := by
  simpa only [Nat.zero_add] using gapBound_b0

end PlanarHom.ColoringMacroFaces.TestFramed
