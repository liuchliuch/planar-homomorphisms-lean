import PlanarHom.ColoringMacroWireFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertexRootBound_b0 : ∀ i : Fin 48, vertexRootValue (0+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b1 : ∀ i : Fin 48, vertexRootValue (48+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b2 : ∀ i : Fin 48, vertexRootValue (96+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b3 : ∀ i : Fin 48, vertexRootValue (144+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b4 : ∀ i : Fin 48, vertexRootValue (192+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b5 : ∀ i : Fin 48, vertexRootValue (240+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b6 : ∀ i : Fin 48, vertexRootValue (288+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b7 : ∀ i : Fin 48, vertexRootValue (336+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b8 : ∀ i : Fin 48, vertexRootValue (384+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b9 : ∀ i : Fin 48, vertexRootValue (432+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b10 : ∀ i : Fin 48, vertexRootValue (480+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_b11 : ∀ i : Fin 6, vertexRootValue (528+i.val) < 2646 := by decide +kernel

private theorem vertexRootBound_n0_0 : ∀ i : Fin 96, vertexRootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 0 48 48 vertexRootBound_b0 vertexRootBound_b1

private theorem vertexRootBound_n0_1 : ∀ i : Fin 96, vertexRootValue (96+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 96 48 48 vertexRootBound_b2 vertexRootBound_b3

private theorem vertexRootBound_n0_2 : ∀ i : Fin 96, vertexRootValue (192+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 192 48 48 vertexRootBound_b4 vertexRootBound_b5

private theorem vertexRootBound_n0_3 : ∀ i : Fin 96, vertexRootValue (288+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 288 48 48 vertexRootBound_b6 vertexRootBound_b7

private theorem vertexRootBound_n0_4 : ∀ i : Fin 96, vertexRootValue (384+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 384 48 48 vertexRootBound_b8 vertexRootBound_b9

private theorem vertexRootBound_n0_5 : ∀ i : Fin 54, vertexRootValue (480+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 480 48 6 vertexRootBound_b10 vertexRootBound_b11

private theorem vertexRootBound_n1_0 : ∀ i : Fin 192, vertexRootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 0 96 96 vertexRootBound_n0_0 vertexRootBound_n0_1

private theorem vertexRootBound_n1_1 : ∀ i : Fin 192, vertexRootValue (192+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 192 96 96 vertexRootBound_n0_2 vertexRootBound_n0_3

private theorem vertexRootBound_n1_2 : ∀ i : Fin 150, vertexRootValue (384+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 384 96 54 vertexRootBound_n0_4 vertexRootBound_n0_5

private theorem vertexRootBound_n2_0 : ∀ i : Fin 384, vertexRootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 0 192 192 vertexRootBound_n1_0 vertexRootBound_n1_1

private theorem vertexRootBound_n3_0 : ∀ i : Fin 534, vertexRootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 2646) 0 384 150 vertexRootBound_n2_0 vertexRootBound_n1_2

theorem vertexRootBound : ∀ i : Fin 534, vertexRootValue i.val < 2646 := by
  simpa only [Nat.zero_add] using vertexRootBound_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
