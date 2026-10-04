import PlanarHom.ColoringMacroCrossFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.CrossFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem parentEdgeBound_b0 : ∀ i : Fin 48, parentEdgeValue (0+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b1 : ∀ i : Fin 48, parentEdgeValue (48+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b2 : ∀ i : Fin 48, parentEdgeValue (96+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b3 : ∀ i : Fin 48, parentEdgeValue (144+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b4 : ∀ i : Fin 48, parentEdgeValue (192+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b5 : ∀ i : Fin 48, parentEdgeValue (240+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b6 : ∀ i : Fin 48, parentEdgeValue (288+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b7 : ∀ i : Fin 48, parentEdgeValue (336+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b8 : ∀ i : Fin 48, parentEdgeValue (384+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b9 : ∀ i : Fin 48, parentEdgeValue (432+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b10 : ∀ i : Fin 48, parentEdgeValue (480+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b11 : ∀ i : Fin 48, parentEdgeValue (528+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b12 : ∀ i : Fin 48, parentEdgeValue (576+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b13 : ∀ i : Fin 48, parentEdgeValue (624+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b14 : ∀ i : Fin 48, parentEdgeValue (672+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b15 : ∀ i : Fin 48, parentEdgeValue (720+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b16 : ∀ i : Fin 48, parentEdgeValue (768+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b17 : ∀ i : Fin 48, parentEdgeValue (816+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b18 : ∀ i : Fin 48, parentEdgeValue (864+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b19 : ∀ i : Fin 48, parentEdgeValue (912+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b20 : ∀ i : Fin 48, parentEdgeValue (960+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b21 : ∀ i : Fin 48, parentEdgeValue (1008+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b22 : ∀ i : Fin 48, parentEdgeValue (1056+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b23 : ∀ i : Fin 48, parentEdgeValue (1104+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b24 : ∀ i : Fin 48, parentEdgeValue (1152+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b25 : ∀ i : Fin 48, parentEdgeValue (1200+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_b26 : ∀ i : Fin 26, parentEdgeValue (1248+i.val) < 3168 := by decide +kernel

private theorem parentEdgeBound_n0_0 : ∀ i : Fin 96, parentEdgeValue (0+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 0 48 48 parentEdgeBound_b0 parentEdgeBound_b1

private theorem parentEdgeBound_n0_1 : ∀ i : Fin 96, parentEdgeValue (96+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 96 48 48 parentEdgeBound_b2 parentEdgeBound_b3

private theorem parentEdgeBound_n0_2 : ∀ i : Fin 96, parentEdgeValue (192+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 192 48 48 parentEdgeBound_b4 parentEdgeBound_b5

private theorem parentEdgeBound_n0_3 : ∀ i : Fin 96, parentEdgeValue (288+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 288 48 48 parentEdgeBound_b6 parentEdgeBound_b7

private theorem parentEdgeBound_n0_4 : ∀ i : Fin 96, parentEdgeValue (384+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 384 48 48 parentEdgeBound_b8 parentEdgeBound_b9

private theorem parentEdgeBound_n0_5 : ∀ i : Fin 96, parentEdgeValue (480+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 480 48 48 parentEdgeBound_b10 parentEdgeBound_b11

private theorem parentEdgeBound_n0_6 : ∀ i : Fin 96, parentEdgeValue (576+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 576 48 48 parentEdgeBound_b12 parentEdgeBound_b13

private theorem parentEdgeBound_n0_7 : ∀ i : Fin 96, parentEdgeValue (672+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 672 48 48 parentEdgeBound_b14 parentEdgeBound_b15

private theorem parentEdgeBound_n0_8 : ∀ i : Fin 96, parentEdgeValue (768+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 768 48 48 parentEdgeBound_b16 parentEdgeBound_b17

private theorem parentEdgeBound_n0_9 : ∀ i : Fin 96, parentEdgeValue (864+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 864 48 48 parentEdgeBound_b18 parentEdgeBound_b19

private theorem parentEdgeBound_n0_10 : ∀ i : Fin 96, parentEdgeValue (960+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 960 48 48 parentEdgeBound_b20 parentEdgeBound_b21

private theorem parentEdgeBound_n0_11 : ∀ i : Fin 96, parentEdgeValue (1056+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 1056 48 48 parentEdgeBound_b22 parentEdgeBound_b23

private theorem parentEdgeBound_n0_12 : ∀ i : Fin 96, parentEdgeValue (1152+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 1152 48 48 parentEdgeBound_b24 parentEdgeBound_b25

private theorem parentEdgeBound_n1_0 : ∀ i : Fin 192, parentEdgeValue (0+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 0 96 96 parentEdgeBound_n0_0 parentEdgeBound_n0_1

private theorem parentEdgeBound_n1_1 : ∀ i : Fin 192, parentEdgeValue (192+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 192 96 96 parentEdgeBound_n0_2 parentEdgeBound_n0_3

private theorem parentEdgeBound_n1_2 : ∀ i : Fin 192, parentEdgeValue (384+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 384 96 96 parentEdgeBound_n0_4 parentEdgeBound_n0_5

private theorem parentEdgeBound_n1_3 : ∀ i : Fin 192, parentEdgeValue (576+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 576 96 96 parentEdgeBound_n0_6 parentEdgeBound_n0_7

private theorem parentEdgeBound_n1_4 : ∀ i : Fin 192, parentEdgeValue (768+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 768 96 96 parentEdgeBound_n0_8 parentEdgeBound_n0_9

private theorem parentEdgeBound_n1_5 : ∀ i : Fin 192, parentEdgeValue (960+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 960 96 96 parentEdgeBound_n0_10 parentEdgeBound_n0_11

private theorem parentEdgeBound_n1_6 : ∀ i : Fin 122, parentEdgeValue (1152+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 1152 96 26 parentEdgeBound_n0_12 parentEdgeBound_b26

private theorem parentEdgeBound_n2_0 : ∀ i : Fin 384, parentEdgeValue (0+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 0 192 192 parentEdgeBound_n1_0 parentEdgeBound_n1_1

private theorem parentEdgeBound_n2_1 : ∀ i : Fin 384, parentEdgeValue (384+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 384 192 192 parentEdgeBound_n1_2 parentEdgeBound_n1_3

private theorem parentEdgeBound_n2_2 : ∀ i : Fin 384, parentEdgeValue (768+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 768 192 192 parentEdgeBound_n1_4 parentEdgeBound_n1_5

private theorem parentEdgeBound_n3_0 : ∀ i : Fin 768, parentEdgeValue (0+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 0 384 384 parentEdgeBound_n2_0 parentEdgeBound_n2_1

private theorem parentEdgeBound_n3_1 : ∀ i : Fin 506, parentEdgeValue (768+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 768 384 122 parentEdgeBound_n2_2 parentEdgeBound_n1_6

private theorem parentEdgeBound_n4_0 : ∀ i : Fin 1274, parentEdgeValue (0+i.val) < 3168 :=
  FiniteIntervalCheck.append (fun i => parentEdgeValue i < 3168) 0 768 506 parentEdgeBound_n3_0 parentEdgeBound_n3_1

theorem parentEdgeBound : ∀ i : Fin 1274, parentEdgeValue i.val < 3168 := by
  simpa only [Nat.zero_add] using parentEdgeBound_n4_0

end PlanarHom.ColoringMacroFaces.CrossFramed
