import PlanarHom.ColoringMacroCrossFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.CrossFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem parentBound_b0 : ∀ i : Fin 48, parentValue (0+i.val) < 1274 := by decide +kernel

private theorem parentBound_b1 : ∀ i : Fin 48, parentValue (48+i.val) < 1274 := by decide +kernel

private theorem parentBound_b2 : ∀ i : Fin 48, parentValue (96+i.val) < 1274 := by decide +kernel

private theorem parentBound_b3 : ∀ i : Fin 48, parentValue (144+i.val) < 1274 := by decide +kernel

private theorem parentBound_b4 : ∀ i : Fin 48, parentValue (192+i.val) < 1274 := by decide +kernel

private theorem parentBound_b5 : ∀ i : Fin 48, parentValue (240+i.val) < 1274 := by decide +kernel

private theorem parentBound_b6 : ∀ i : Fin 48, parentValue (288+i.val) < 1274 := by decide +kernel

private theorem parentBound_b7 : ∀ i : Fin 48, parentValue (336+i.val) < 1274 := by decide +kernel

private theorem parentBound_b8 : ∀ i : Fin 48, parentValue (384+i.val) < 1274 := by decide +kernel

private theorem parentBound_b9 : ∀ i : Fin 48, parentValue (432+i.val) < 1274 := by decide +kernel

private theorem parentBound_b10 : ∀ i : Fin 48, parentValue (480+i.val) < 1274 := by decide +kernel

private theorem parentBound_b11 : ∀ i : Fin 48, parentValue (528+i.val) < 1274 := by decide +kernel

private theorem parentBound_b12 : ∀ i : Fin 48, parentValue (576+i.val) < 1274 := by decide +kernel

private theorem parentBound_b13 : ∀ i : Fin 48, parentValue (624+i.val) < 1274 := by decide +kernel

private theorem parentBound_b14 : ∀ i : Fin 48, parentValue (672+i.val) < 1274 := by decide +kernel

private theorem parentBound_b15 : ∀ i : Fin 48, parentValue (720+i.val) < 1274 := by decide +kernel

private theorem parentBound_b16 : ∀ i : Fin 48, parentValue (768+i.val) < 1274 := by decide +kernel

private theorem parentBound_b17 : ∀ i : Fin 48, parentValue (816+i.val) < 1274 := by decide +kernel

private theorem parentBound_b18 : ∀ i : Fin 48, parentValue (864+i.val) < 1274 := by decide +kernel

private theorem parentBound_b19 : ∀ i : Fin 48, parentValue (912+i.val) < 1274 := by decide +kernel

private theorem parentBound_b20 : ∀ i : Fin 48, parentValue (960+i.val) < 1274 := by decide +kernel

private theorem parentBound_b21 : ∀ i : Fin 48, parentValue (1008+i.val) < 1274 := by decide +kernel

private theorem parentBound_b22 : ∀ i : Fin 48, parentValue (1056+i.val) < 1274 := by decide +kernel

private theorem parentBound_b23 : ∀ i : Fin 48, parentValue (1104+i.val) < 1274 := by decide +kernel

private theorem parentBound_b24 : ∀ i : Fin 48, parentValue (1152+i.val) < 1274 := by decide +kernel

private theorem parentBound_b25 : ∀ i : Fin 48, parentValue (1200+i.val) < 1274 := by decide +kernel

private theorem parentBound_b26 : ∀ i : Fin 26, parentValue (1248+i.val) < 1274 := by decide +kernel

private theorem parentBound_n0_0 : ∀ i : Fin 96, parentValue (0+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 0 48 48 parentBound_b0 parentBound_b1

private theorem parentBound_n0_1 : ∀ i : Fin 96, parentValue (96+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 96 48 48 parentBound_b2 parentBound_b3

private theorem parentBound_n0_2 : ∀ i : Fin 96, parentValue (192+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 192 48 48 parentBound_b4 parentBound_b5

private theorem parentBound_n0_3 : ∀ i : Fin 96, parentValue (288+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 288 48 48 parentBound_b6 parentBound_b7

private theorem parentBound_n0_4 : ∀ i : Fin 96, parentValue (384+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 384 48 48 parentBound_b8 parentBound_b9

private theorem parentBound_n0_5 : ∀ i : Fin 96, parentValue (480+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 480 48 48 parentBound_b10 parentBound_b11

private theorem parentBound_n0_6 : ∀ i : Fin 96, parentValue (576+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 576 48 48 parentBound_b12 parentBound_b13

private theorem parentBound_n0_7 : ∀ i : Fin 96, parentValue (672+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 672 48 48 parentBound_b14 parentBound_b15

private theorem parentBound_n0_8 : ∀ i : Fin 96, parentValue (768+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 768 48 48 parentBound_b16 parentBound_b17

private theorem parentBound_n0_9 : ∀ i : Fin 96, parentValue (864+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 864 48 48 parentBound_b18 parentBound_b19

private theorem parentBound_n0_10 : ∀ i : Fin 96, parentValue (960+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 960 48 48 parentBound_b20 parentBound_b21

private theorem parentBound_n0_11 : ∀ i : Fin 96, parentValue (1056+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 1056 48 48 parentBound_b22 parentBound_b23

private theorem parentBound_n0_12 : ∀ i : Fin 96, parentValue (1152+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 1152 48 48 parentBound_b24 parentBound_b25

private theorem parentBound_n1_0 : ∀ i : Fin 192, parentValue (0+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 0 96 96 parentBound_n0_0 parentBound_n0_1

private theorem parentBound_n1_1 : ∀ i : Fin 192, parentValue (192+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 192 96 96 parentBound_n0_2 parentBound_n0_3

private theorem parentBound_n1_2 : ∀ i : Fin 192, parentValue (384+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 384 96 96 parentBound_n0_4 parentBound_n0_5

private theorem parentBound_n1_3 : ∀ i : Fin 192, parentValue (576+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 576 96 96 parentBound_n0_6 parentBound_n0_7

private theorem parentBound_n1_4 : ∀ i : Fin 192, parentValue (768+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 768 96 96 parentBound_n0_8 parentBound_n0_9

private theorem parentBound_n1_5 : ∀ i : Fin 192, parentValue (960+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 960 96 96 parentBound_n0_10 parentBound_n0_11

private theorem parentBound_n1_6 : ∀ i : Fin 122, parentValue (1152+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 1152 96 26 parentBound_n0_12 parentBound_b26

private theorem parentBound_n2_0 : ∀ i : Fin 384, parentValue (0+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 0 192 192 parentBound_n1_0 parentBound_n1_1

private theorem parentBound_n2_1 : ∀ i : Fin 384, parentValue (384+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 384 192 192 parentBound_n1_2 parentBound_n1_3

private theorem parentBound_n2_2 : ∀ i : Fin 384, parentValue (768+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 768 192 192 parentBound_n1_4 parentBound_n1_5

private theorem parentBound_n3_0 : ∀ i : Fin 768, parentValue (0+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 0 384 384 parentBound_n2_0 parentBound_n2_1

private theorem parentBound_n3_1 : ∀ i : Fin 506, parentValue (768+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 768 384 122 parentBound_n2_2 parentBound_n1_6

private theorem parentBound_n4_0 : ∀ i : Fin 1274, parentValue (0+i.val) < 1274 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 1274) 0 768 506 parentBound_n3_0 parentBound_n3_1

theorem parentBound : ∀ i : Fin 1274, parentValue i.val < 1274 := by
  simpa only [Nat.zero_add] using parentBound_n4_0

end PlanarHom.ColoringMacroFaces.CrossFramed
