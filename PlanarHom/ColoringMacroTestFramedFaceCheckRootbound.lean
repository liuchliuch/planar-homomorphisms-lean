import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem rootBound_b0 : ∀ i : Fin 48, rootValue (0+i.val) < 570 := by decide +kernel

private theorem rootBound_b1 : ∀ i : Fin 48, rootValue (48+i.val) < 570 := by decide +kernel

private theorem rootBound_b2 : ∀ i : Fin 48, rootValue (96+i.val) < 570 := by decide +kernel

private theorem rootBound_b3 : ∀ i : Fin 25, rootValue (144+i.val) < 570 := by decide +kernel

private theorem rootBound_n0_0 : ∀ i : Fin 96, rootValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 570) 0 48 48 rootBound_b0 rootBound_b1

private theorem rootBound_n0_1 : ∀ i : Fin 73, rootValue (96+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 570) 96 48 25 rootBound_b2 rootBound_b3

private theorem rootBound_n1_0 : ∀ i : Fin 169, rootValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 570) 0 96 73 rootBound_n0_0 rootBound_n0_1

theorem rootBound : ∀ i : Fin 169, rootValue i.val < 570 := by
  simpa only [Nat.zero_add] using rootBound_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
