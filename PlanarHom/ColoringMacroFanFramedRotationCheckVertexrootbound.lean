import PlanarHom.ColoringMacroFanFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.FanFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertexRootBound_b0 : ∀ i : Fin 48, vertexRootValue (0+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b1 : ∀ i : Fin 48, vertexRootValue (48+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b2 : ∀ i : Fin 48, vertexRootValue (96+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b3 : ∀ i : Fin 48, vertexRootValue (144+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b4 : ∀ i : Fin 48, vertexRootValue (192+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b5 : ∀ i : Fin 48, vertexRootValue (240+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b6 : ∀ i : Fin 48, vertexRootValue (288+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b7 : ∀ i : Fin 48, vertexRootValue (336+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b8 : ∀ i : Fin 48, vertexRootValue (384+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b9 : ∀ i : Fin 48, vertexRootValue (432+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b10 : ∀ i : Fin 48, vertexRootValue (480+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b11 : ∀ i : Fin 48, vertexRootValue (528+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b12 : ∀ i : Fin 48, vertexRootValue (576+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b13 : ∀ i : Fin 48, vertexRootValue (624+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b14 : ∀ i : Fin 48, vertexRootValue (672+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b15 : ∀ i : Fin 48, vertexRootValue (720+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b16 : ∀ i : Fin 48, vertexRootValue (768+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b17 : ∀ i : Fin 48, vertexRootValue (816+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b18 : ∀ i : Fin 48, vertexRootValue (864+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b19 : ∀ i : Fin 48, vertexRootValue (912+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b20 : ∀ i : Fin 48, vertexRootValue (960+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b21 : ∀ i : Fin 48, vertexRootValue (1008+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_b22 : ∀ i : Fin 2, vertexRootValue (1056+i.val) < 5264 := by decide +kernel

private theorem vertexRootBound_n0_0 : ∀ i : Fin 96, vertexRootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 0 48 48 vertexRootBound_b0 vertexRootBound_b1

private theorem vertexRootBound_n0_1 : ∀ i : Fin 96, vertexRootValue (96+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 96 48 48 vertexRootBound_b2 vertexRootBound_b3

private theorem vertexRootBound_n0_2 : ∀ i : Fin 96, vertexRootValue (192+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 192 48 48 vertexRootBound_b4 vertexRootBound_b5

private theorem vertexRootBound_n0_3 : ∀ i : Fin 96, vertexRootValue (288+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 288 48 48 vertexRootBound_b6 vertexRootBound_b7

private theorem vertexRootBound_n0_4 : ∀ i : Fin 96, vertexRootValue (384+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 384 48 48 vertexRootBound_b8 vertexRootBound_b9

private theorem vertexRootBound_n0_5 : ∀ i : Fin 96, vertexRootValue (480+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 480 48 48 vertexRootBound_b10 vertexRootBound_b11

private theorem vertexRootBound_n0_6 : ∀ i : Fin 96, vertexRootValue (576+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 576 48 48 vertexRootBound_b12 vertexRootBound_b13

private theorem vertexRootBound_n0_7 : ∀ i : Fin 96, vertexRootValue (672+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 672 48 48 vertexRootBound_b14 vertexRootBound_b15

private theorem vertexRootBound_n0_8 : ∀ i : Fin 96, vertexRootValue (768+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 768 48 48 vertexRootBound_b16 vertexRootBound_b17

private theorem vertexRootBound_n0_9 : ∀ i : Fin 96, vertexRootValue (864+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 864 48 48 vertexRootBound_b18 vertexRootBound_b19

private theorem vertexRootBound_n0_10 : ∀ i : Fin 96, vertexRootValue (960+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 960 48 48 vertexRootBound_b20 vertexRootBound_b21

private theorem vertexRootBound_n1_0 : ∀ i : Fin 192, vertexRootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 0 96 96 vertexRootBound_n0_0 vertexRootBound_n0_1

private theorem vertexRootBound_n1_1 : ∀ i : Fin 192, vertexRootValue (192+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 192 96 96 vertexRootBound_n0_2 vertexRootBound_n0_3

private theorem vertexRootBound_n1_2 : ∀ i : Fin 192, vertexRootValue (384+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 384 96 96 vertexRootBound_n0_4 vertexRootBound_n0_5

private theorem vertexRootBound_n1_3 : ∀ i : Fin 192, vertexRootValue (576+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 576 96 96 vertexRootBound_n0_6 vertexRootBound_n0_7

private theorem vertexRootBound_n1_4 : ∀ i : Fin 192, vertexRootValue (768+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 768 96 96 vertexRootBound_n0_8 vertexRootBound_n0_9

private theorem vertexRootBound_n1_5 : ∀ i : Fin 98, vertexRootValue (960+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 960 96 2 vertexRootBound_n0_10 vertexRootBound_b22

private theorem vertexRootBound_n2_0 : ∀ i : Fin 384, vertexRootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 0 192 192 vertexRootBound_n1_0 vertexRootBound_n1_1

private theorem vertexRootBound_n2_1 : ∀ i : Fin 384, vertexRootValue (384+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 384 192 192 vertexRootBound_n1_2 vertexRootBound_n1_3

private theorem vertexRootBound_n2_2 : ∀ i : Fin 290, vertexRootValue (768+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 768 192 98 vertexRootBound_n1_4 vertexRootBound_n1_5

private theorem vertexRootBound_n3_0 : ∀ i : Fin 768, vertexRootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 0 384 384 vertexRootBound_n2_0 vertexRootBound_n2_1

private theorem vertexRootBound_n4_0 : ∀ i : Fin 1058, vertexRootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => vertexRootValue i < 5264) 0 768 290 vertexRootBound_n3_0 vertexRootBound_n2_2

theorem vertexRootBound : ∀ i : Fin 1058, vertexRootValue i.val < 5264 := by
  simpa only [Nat.zero_add] using vertexRootBound_n4_0

end PlanarHom.ColoringMacroFaces.FanFramed
