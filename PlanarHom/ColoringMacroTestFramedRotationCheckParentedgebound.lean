import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem parentEdgeBound_b0 : ∀ i : Fin 48, parentEdgeValue (0+i.val) < 285 := by decide +kernel

private theorem parentEdgeBound_b1 : ∀ i : Fin 48, parentEdgeValue (48+i.val) < 285 := by decide +kernel

private theorem parentEdgeBound_b2 : ∀ i : Fin 22, parentEdgeValue (96+i.val) < 285 := by decide +kernel

private theorem parentEdgeBound_n0_0 : ∀ i : Fin 96, parentEdgeValue (0+i.val) < 285 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 285) 0 48 48 parentEdgeBound_b0 parentEdgeBound_b1

private theorem parentEdgeBound_n1_0 : ∀ i : Fin 118, parentEdgeValue (0+i.val) < 285 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 285) 0 96 22 parentEdgeBound_n0_0 parentEdgeBound_b2

theorem parentEdgeBound : ∀ i : Fin 118, parentEdgeValue i.val < 285 := by
  simpa only [Nat.zero_add] using parentEdgeBound_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
