import PlanarHom.ColoringMacroCrossFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.CrossFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem gapBound_b0 : ∀ i : Fin 16, gapValue (0+i.val) < 6336 := by decide +kernel

theorem gapBound : ∀ i : Fin 16, gapValue i.val < 6336 := by
  simpa only [Nat.zero_add] using gapBound_b0

end PlanarHom.ColoringMacroFaces.CrossFramed
