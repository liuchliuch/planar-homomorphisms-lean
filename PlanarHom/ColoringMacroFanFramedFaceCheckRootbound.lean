import PlanarHom.ColoringMacroFanFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.FanFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem rootBound_b0 : ∀ i : Fin 48, rootValue (0+i.val) < 5264 := by decide +kernel

private theorem rootBound_b1 : ∀ i : Fin 48, rootValue (48+i.val) < 5264 := by decide +kernel

private theorem rootBound_b2 : ∀ i : Fin 48, rootValue (96+i.val) < 5264 := by decide +kernel

private theorem rootBound_b3 : ∀ i : Fin 48, rootValue (144+i.val) < 5264 := by decide +kernel

private theorem rootBound_b4 : ∀ i : Fin 48, rootValue (192+i.val) < 5264 := by decide +kernel

private theorem rootBound_b5 : ∀ i : Fin 48, rootValue (240+i.val) < 5264 := by decide +kernel

private theorem rootBound_b6 : ∀ i : Fin 48, rootValue (288+i.val) < 5264 := by decide +kernel

private theorem rootBound_b7 : ∀ i : Fin 48, rootValue (336+i.val) < 5264 := by decide +kernel

private theorem rootBound_b8 : ∀ i : Fin 48, rootValue (384+i.val) < 5264 := by decide +kernel

private theorem rootBound_b9 : ∀ i : Fin 48, rootValue (432+i.val) < 5264 := by decide +kernel

private theorem rootBound_b10 : ∀ i : Fin 48, rootValue (480+i.val) < 5264 := by decide +kernel

private theorem rootBound_b11 : ∀ i : Fin 48, rootValue (528+i.val) < 5264 := by decide +kernel

private theorem rootBound_b12 : ∀ i : Fin 48, rootValue (576+i.val) < 5264 := by decide +kernel

private theorem rootBound_b13 : ∀ i : Fin 48, rootValue (624+i.val) < 5264 := by decide +kernel

private theorem rootBound_b14 : ∀ i : Fin 48, rootValue (672+i.val) < 5264 := by decide +kernel

private theorem rootBound_b15 : ∀ i : Fin 48, rootValue (720+i.val) < 5264 := by decide +kernel

private theorem rootBound_b16 : ∀ i : Fin 48, rootValue (768+i.val) < 5264 := by decide +kernel

private theorem rootBound_b17 : ∀ i : Fin 48, rootValue (816+i.val) < 5264 := by decide +kernel

private theorem rootBound_b18 : ∀ i : Fin 48, rootValue (864+i.val) < 5264 := by decide +kernel

private theorem rootBound_b19 : ∀ i : Fin 48, rootValue (912+i.val) < 5264 := by decide +kernel

private theorem rootBound_b20 : ∀ i : Fin 48, rootValue (960+i.val) < 5264 := by decide +kernel

private theorem rootBound_b21 : ∀ i : Fin 48, rootValue (1008+i.val) < 5264 := by decide +kernel

private theorem rootBound_b22 : ∀ i : Fin 48, rootValue (1056+i.val) < 5264 := by decide +kernel

private theorem rootBound_b23 : ∀ i : Fin 48, rootValue (1104+i.val) < 5264 := by decide +kernel

private theorem rootBound_b24 : ∀ i : Fin 48, rootValue (1152+i.val) < 5264 := by decide +kernel

private theorem rootBound_b25 : ∀ i : Fin 48, rootValue (1200+i.val) < 5264 := by decide +kernel

private theorem rootBound_b26 : ∀ i : Fin 48, rootValue (1248+i.val) < 5264 := by decide +kernel

private theorem rootBound_b27 : ∀ i : Fin 48, rootValue (1296+i.val) < 5264 := by decide +kernel

private theorem rootBound_b28 : ∀ i : Fin 48, rootValue (1344+i.val) < 5264 := by decide +kernel

private theorem rootBound_b29 : ∀ i : Fin 48, rootValue (1392+i.val) < 5264 := by decide +kernel

private theorem rootBound_b30 : ∀ i : Fin 48, rootValue (1440+i.val) < 5264 := by decide +kernel

private theorem rootBound_b31 : ∀ i : Fin 48, rootValue (1488+i.val) < 5264 := by decide +kernel

private theorem rootBound_b32 : ∀ i : Fin 40, rootValue (1536+i.val) < 5264 := by decide +kernel

private theorem rootBound_n0_0 : ∀ i : Fin 96, rootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 0 48 48 rootBound_b0 rootBound_b1

private theorem rootBound_n0_1 : ∀ i : Fin 96, rootValue (96+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 96 48 48 rootBound_b2 rootBound_b3

private theorem rootBound_n0_2 : ∀ i : Fin 96, rootValue (192+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 192 48 48 rootBound_b4 rootBound_b5

private theorem rootBound_n0_3 : ∀ i : Fin 96, rootValue (288+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 288 48 48 rootBound_b6 rootBound_b7

private theorem rootBound_n0_4 : ∀ i : Fin 96, rootValue (384+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 384 48 48 rootBound_b8 rootBound_b9

private theorem rootBound_n0_5 : ∀ i : Fin 96, rootValue (480+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 480 48 48 rootBound_b10 rootBound_b11

private theorem rootBound_n0_6 : ∀ i : Fin 96, rootValue (576+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 576 48 48 rootBound_b12 rootBound_b13

private theorem rootBound_n0_7 : ∀ i : Fin 96, rootValue (672+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 672 48 48 rootBound_b14 rootBound_b15

private theorem rootBound_n0_8 : ∀ i : Fin 96, rootValue (768+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 768 48 48 rootBound_b16 rootBound_b17

private theorem rootBound_n0_9 : ∀ i : Fin 96, rootValue (864+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 864 48 48 rootBound_b18 rootBound_b19

private theorem rootBound_n0_10 : ∀ i : Fin 96, rootValue (960+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 960 48 48 rootBound_b20 rootBound_b21

private theorem rootBound_n0_11 : ∀ i : Fin 96, rootValue (1056+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 1056 48 48 rootBound_b22 rootBound_b23

private theorem rootBound_n0_12 : ∀ i : Fin 96, rootValue (1152+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 1152 48 48 rootBound_b24 rootBound_b25

private theorem rootBound_n0_13 : ∀ i : Fin 96, rootValue (1248+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 1248 48 48 rootBound_b26 rootBound_b27

private theorem rootBound_n0_14 : ∀ i : Fin 96, rootValue (1344+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 1344 48 48 rootBound_b28 rootBound_b29

private theorem rootBound_n0_15 : ∀ i : Fin 96, rootValue (1440+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 1440 48 48 rootBound_b30 rootBound_b31

private theorem rootBound_n1_0 : ∀ i : Fin 192, rootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 0 96 96 rootBound_n0_0 rootBound_n0_1

private theorem rootBound_n1_1 : ∀ i : Fin 192, rootValue (192+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 192 96 96 rootBound_n0_2 rootBound_n0_3

private theorem rootBound_n1_2 : ∀ i : Fin 192, rootValue (384+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 384 96 96 rootBound_n0_4 rootBound_n0_5

private theorem rootBound_n1_3 : ∀ i : Fin 192, rootValue (576+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 576 96 96 rootBound_n0_6 rootBound_n0_7

private theorem rootBound_n1_4 : ∀ i : Fin 192, rootValue (768+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 768 96 96 rootBound_n0_8 rootBound_n0_9

private theorem rootBound_n1_5 : ∀ i : Fin 192, rootValue (960+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 960 96 96 rootBound_n0_10 rootBound_n0_11

private theorem rootBound_n1_6 : ∀ i : Fin 192, rootValue (1152+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 1152 96 96 rootBound_n0_12 rootBound_n0_13

private theorem rootBound_n1_7 : ∀ i : Fin 192, rootValue (1344+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 1344 96 96 rootBound_n0_14 rootBound_n0_15

private theorem rootBound_n2_0 : ∀ i : Fin 384, rootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 0 192 192 rootBound_n1_0 rootBound_n1_1

private theorem rootBound_n2_1 : ∀ i : Fin 384, rootValue (384+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 384 192 192 rootBound_n1_2 rootBound_n1_3

private theorem rootBound_n2_2 : ∀ i : Fin 384, rootValue (768+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 768 192 192 rootBound_n1_4 rootBound_n1_5

private theorem rootBound_n2_3 : ∀ i : Fin 384, rootValue (1152+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 1152 192 192 rootBound_n1_6 rootBound_n1_7

private theorem rootBound_n3_0 : ∀ i : Fin 768, rootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 0 384 384 rootBound_n2_0 rootBound_n2_1

private theorem rootBound_n3_1 : ∀ i : Fin 768, rootValue (768+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 768 384 384 rootBound_n2_2 rootBound_n2_3

private theorem rootBound_n4_0 : ∀ i : Fin 1536, rootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 0 768 768 rootBound_n3_0 rootBound_n3_1

private theorem rootBound_n5_0 : ∀ i : Fin 1576, rootValue (0+i.val) < 5264 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 5264) 0 1536 40 rootBound_n4_0 rootBound_b32

theorem rootBound : ∀ i : Fin 1576, rootValue i.val < 5264 := by
  simpa only [Nat.zero_add] using rootBound_n5_0

end PlanarHom.ColoringMacroFaces.FanFramed
