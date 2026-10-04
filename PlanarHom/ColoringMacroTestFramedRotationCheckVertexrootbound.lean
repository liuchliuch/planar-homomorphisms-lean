import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertexRootBound_b0 : ∀ i : Fin 48, vertexRootValue (0+i.val) < 570 := by decide +kernel

private theorem vertexRootBound_b1 : ∀ i : Fin 48, vertexRootValue (48+i.val) < 570 := by decide +kernel

private theorem vertexRootBound_b2 : ∀ i : Fin 22, vertexRootValue (96+i.val) < 570 := by decide +kernel

private theorem vertexRootBound_n0_0 : ∀ i : Fin 96, vertexRootValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 570) 0 48 48 vertexRootBound_b0 vertexRootBound_b1

private theorem vertexRootBound_n1_0 : ∀ i : Fin 118, vertexRootValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 570) 0 96 22 vertexRootBound_n0_0 vertexRootBound_b2

theorem vertexRootBound : ∀ i : Fin 118, vertexRootValue i.val < 570 := by
  simpa only [Nat.zero_add] using vertexRootBound_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
