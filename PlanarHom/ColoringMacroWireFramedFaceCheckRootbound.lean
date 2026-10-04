import PlanarHom.ColoringMacroWireFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem rootBound_b0 : ∀ i : Fin 48, rootValue (0+i.val) < 2646 := by decide +kernel

private theorem rootBound_b1 : ∀ i : Fin 48, rootValue (48+i.val) < 2646 := by decide +kernel

private theorem rootBound_b2 : ∀ i : Fin 48, rootValue (96+i.val) < 2646 := by decide +kernel

private theorem rootBound_b3 : ∀ i : Fin 48, rootValue (144+i.val) < 2646 := by decide +kernel

private theorem rootBound_b4 : ∀ i : Fin 48, rootValue (192+i.val) < 2646 := by decide +kernel

private theorem rootBound_b5 : ∀ i : Fin 48, rootValue (240+i.val) < 2646 := by decide +kernel

private theorem rootBound_b6 : ∀ i : Fin 48, rootValue (288+i.val) < 2646 := by decide +kernel

private theorem rootBound_b7 : ∀ i : Fin 48, rootValue (336+i.val) < 2646 := by decide +kernel

private theorem rootBound_b8 : ∀ i : Fin 48, rootValue (384+i.val) < 2646 := by decide +kernel

private theorem rootBound_b9 : ∀ i : Fin 48, rootValue (432+i.val) < 2646 := by decide +kernel

private theorem rootBound_b10 : ∀ i : Fin 48, rootValue (480+i.val) < 2646 := by decide +kernel

private theorem rootBound_b11 : ∀ i : Fin 48, rootValue (528+i.val) < 2646 := by decide +kernel

private theorem rootBound_b12 : ∀ i : Fin 48, rootValue (576+i.val) < 2646 := by decide +kernel

private theorem rootBound_b13 : ∀ i : Fin 48, rootValue (624+i.val) < 2646 := by decide +kernel

private theorem rootBound_b14 : ∀ i : Fin 48, rootValue (672+i.val) < 2646 := by decide +kernel

private theorem rootBound_b15 : ∀ i : Fin 48, rootValue (720+i.val) < 2646 := by decide +kernel

private theorem rootBound_b16 : ∀ i : Fin 23, rootValue (768+i.val) < 2646 := by decide +kernel

private theorem rootBound_n0_0 : ∀ i : Fin 96, rootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 0 48 48 rootBound_b0 rootBound_b1

private theorem rootBound_n0_1 : ∀ i : Fin 96, rootValue (96+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 96 48 48 rootBound_b2 rootBound_b3

private theorem rootBound_n0_2 : ∀ i : Fin 96, rootValue (192+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 192 48 48 rootBound_b4 rootBound_b5

private theorem rootBound_n0_3 : ∀ i : Fin 96, rootValue (288+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 288 48 48 rootBound_b6 rootBound_b7

private theorem rootBound_n0_4 : ∀ i : Fin 96, rootValue (384+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 384 48 48 rootBound_b8 rootBound_b9

private theorem rootBound_n0_5 : ∀ i : Fin 96, rootValue (480+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 480 48 48 rootBound_b10 rootBound_b11

private theorem rootBound_n0_6 : ∀ i : Fin 96, rootValue (576+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 576 48 48 rootBound_b12 rootBound_b13

private theorem rootBound_n0_7 : ∀ i : Fin 96, rootValue (672+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 672 48 48 rootBound_b14 rootBound_b15

private theorem rootBound_n1_0 : ∀ i : Fin 192, rootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 0 96 96 rootBound_n0_0 rootBound_n0_1

private theorem rootBound_n1_1 : ∀ i : Fin 192, rootValue (192+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 192 96 96 rootBound_n0_2 rootBound_n0_3

private theorem rootBound_n1_2 : ∀ i : Fin 192, rootValue (384+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 384 96 96 rootBound_n0_4 rootBound_n0_5

private theorem rootBound_n1_3 : ∀ i : Fin 192, rootValue (576+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 576 96 96 rootBound_n0_6 rootBound_n0_7

private theorem rootBound_n2_0 : ∀ i : Fin 384, rootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 0 192 192 rootBound_n1_0 rootBound_n1_1

private theorem rootBound_n2_1 : ∀ i : Fin 384, rootValue (384+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 384 192 192 rootBound_n1_2 rootBound_n1_3

private theorem rootBound_n3_0 : ∀ i : Fin 768, rootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 0 384 384 rootBound_n2_0 rootBound_n2_1

private theorem rootBound_n4_0 : ∀ i : Fin 791, rootValue (0+i.val) < 2646 :=
  FiniteIntervalCheck.append (fun i => rootValue i < 2646) 0 768 23 rootBound_n3_0 rootBound_b16

theorem rootBound : ∀ i : Fin 791, rootValue i.val < 2646 := by
  simpa only [Nat.zero_add] using rootBound_n4_0

end PlanarHom.ColoringMacroFaces.WireFramed
