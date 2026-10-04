import PlanarHom.ColoringMacroWireFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem parentEdgeBound_b0 : ∀ i : Fin 48, parentEdgeValue (0+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b1 : ∀ i : Fin 48, parentEdgeValue (48+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b2 : ∀ i : Fin 48, parentEdgeValue (96+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b3 : ∀ i : Fin 48, parentEdgeValue (144+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b4 : ∀ i : Fin 48, parentEdgeValue (192+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b5 : ∀ i : Fin 48, parentEdgeValue (240+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b6 : ∀ i : Fin 48, parentEdgeValue (288+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b7 : ∀ i : Fin 48, parentEdgeValue (336+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b8 : ∀ i : Fin 48, parentEdgeValue (384+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b9 : ∀ i : Fin 48, parentEdgeValue (432+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b10 : ∀ i : Fin 48, parentEdgeValue (480+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_b11 : ∀ i : Fin 6, parentEdgeValue (528+i.val) < 1323 := by decide +kernel

private theorem parentEdgeBound_n0_0 : ∀ i : Fin 96, parentEdgeValue (0+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 0 48 48 parentEdgeBound_b0 parentEdgeBound_b1

private theorem parentEdgeBound_n0_1 : ∀ i : Fin 96, parentEdgeValue (96+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 96 48 48 parentEdgeBound_b2 parentEdgeBound_b3

private theorem parentEdgeBound_n0_2 : ∀ i : Fin 96, parentEdgeValue (192+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 192 48 48 parentEdgeBound_b4 parentEdgeBound_b5

private theorem parentEdgeBound_n0_3 : ∀ i : Fin 96, parentEdgeValue (288+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 288 48 48 parentEdgeBound_b6 parentEdgeBound_b7

private theorem parentEdgeBound_n0_4 : ∀ i : Fin 96, parentEdgeValue (384+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 384 48 48 parentEdgeBound_b8 parentEdgeBound_b9

private theorem parentEdgeBound_n0_5 : ∀ i : Fin 54, parentEdgeValue (480+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 480 48 6 parentEdgeBound_b10 parentEdgeBound_b11

private theorem parentEdgeBound_n1_0 : ∀ i : Fin 192, parentEdgeValue (0+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 0 96 96 parentEdgeBound_n0_0 parentEdgeBound_n0_1

private theorem parentEdgeBound_n1_1 : ∀ i : Fin 192, parentEdgeValue (192+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 192 96 96 parentEdgeBound_n0_2 parentEdgeBound_n0_3

private theorem parentEdgeBound_n1_2 : ∀ i : Fin 150, parentEdgeValue (384+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 384 96 54 parentEdgeBound_n0_4 parentEdgeBound_n0_5

private theorem parentEdgeBound_n2_0 : ∀ i : Fin 384, parentEdgeValue (0+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 0 192 192 parentEdgeBound_n1_0 parentEdgeBound_n1_1

private theorem parentEdgeBound_n3_0 : ∀ i : Fin 534, parentEdgeValue (0+i.val) < 1323 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 1323) 0 384 150 parentEdgeBound_n2_0 parentEdgeBound_n1_2

theorem parentEdgeBound : ∀ i : Fin 534, parentEdgeValue i.val < 1323 := by
  simpa only [Nat.zero_add] using parentEdgeBound_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
