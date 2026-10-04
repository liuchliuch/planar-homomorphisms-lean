import PlanarHom.ColoringMacroCrossFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.CrossFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem connect_zero_root_b0 : ∀ i : Fin 48, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b1 : ∀ i : Fin 48, connectRankValue (48+i.val) = 0 → (48+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b2 : ∀ i : Fin 48, connectRankValue (96+i.val) = 0 → (96+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b3 : ∀ i : Fin 48, connectRankValue (144+i.val) = 0 → (144+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b4 : ∀ i : Fin 48, connectRankValue (192+i.val) = 0 → (192+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b5 : ∀ i : Fin 48, connectRankValue (240+i.val) = 0 → (240+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b6 : ∀ i : Fin 48, connectRankValue (288+i.val) = 0 → (288+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b7 : ∀ i : Fin 48, connectRankValue (336+i.val) = 0 → (336+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b8 : ∀ i : Fin 48, connectRankValue (384+i.val) = 0 → (384+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b9 : ∀ i : Fin 48, connectRankValue (432+i.val) = 0 → (432+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b10 : ∀ i : Fin 48, connectRankValue (480+i.val) = 0 → (480+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b11 : ∀ i : Fin 48, connectRankValue (528+i.val) = 0 → (528+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b12 : ∀ i : Fin 48, connectRankValue (576+i.val) = 0 → (576+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b13 : ∀ i : Fin 48, connectRankValue (624+i.val) = 0 → (624+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b14 : ∀ i : Fin 48, connectRankValue (672+i.val) = 0 → (672+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b15 : ∀ i : Fin 48, connectRankValue (720+i.val) = 0 → (720+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b16 : ∀ i : Fin 48, connectRankValue (768+i.val) = 0 → (768+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b17 : ∀ i : Fin 48, connectRankValue (816+i.val) = 0 → (816+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b18 : ∀ i : Fin 48, connectRankValue (864+i.val) = 0 → (864+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b19 : ∀ i : Fin 48, connectRankValue (912+i.val) = 0 → (912+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b20 : ∀ i : Fin 48, connectRankValue (960+i.val) = 0 → (960+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b21 : ∀ i : Fin 48, connectRankValue (1008+i.val) = 0 → (1008+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b22 : ∀ i : Fin 48, connectRankValue (1056+i.val) = 0 → (1056+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b23 : ∀ i : Fin 48, connectRankValue (1104+i.val) = 0 → (1104+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b24 : ∀ i : Fin 48, connectRankValue (1152+i.val) = 0 → (1152+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b25 : ∀ i : Fin 48, connectRankValue (1200+i.val) = 0 → (1200+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b26 : ∀ i : Fin 26, connectRankValue (1248+i.val) = 0 → (1248+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_n0_0 : ∀ i : Fin 96, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 48 48 connect_zero_root_b0 connect_zero_root_b1

private theorem connect_zero_root_n0_1 : ∀ i : Fin 96, connectRankValue (96+i.val) = 0 → (96+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 96 48 48 connect_zero_root_b2 connect_zero_root_b3

private theorem connect_zero_root_n0_2 : ∀ i : Fin 96, connectRankValue (192+i.val) = 0 → (192+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 192 48 48 connect_zero_root_b4 connect_zero_root_b5

private theorem connect_zero_root_n0_3 : ∀ i : Fin 96, connectRankValue (288+i.val) = 0 → (288+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 288 48 48 connect_zero_root_b6 connect_zero_root_b7

private theorem connect_zero_root_n0_4 : ∀ i : Fin 96, connectRankValue (384+i.val) = 0 → (384+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 384 48 48 connect_zero_root_b8 connect_zero_root_b9

private theorem connect_zero_root_n0_5 : ∀ i : Fin 96, connectRankValue (480+i.val) = 0 → (480+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 480 48 48 connect_zero_root_b10 connect_zero_root_b11

private theorem connect_zero_root_n0_6 : ∀ i : Fin 96, connectRankValue (576+i.val) = 0 → (576+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 576 48 48 connect_zero_root_b12 connect_zero_root_b13

private theorem connect_zero_root_n0_7 : ∀ i : Fin 96, connectRankValue (672+i.val) = 0 → (672+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 672 48 48 connect_zero_root_b14 connect_zero_root_b15

private theorem connect_zero_root_n0_8 : ∀ i : Fin 96, connectRankValue (768+i.val) = 0 → (768+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 768 48 48 connect_zero_root_b16 connect_zero_root_b17

private theorem connect_zero_root_n0_9 : ∀ i : Fin 96, connectRankValue (864+i.val) = 0 → (864+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 864 48 48 connect_zero_root_b18 connect_zero_root_b19

private theorem connect_zero_root_n0_10 : ∀ i : Fin 96, connectRankValue (960+i.val) = 0 → (960+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 960 48 48 connect_zero_root_b20 connect_zero_root_b21

private theorem connect_zero_root_n0_11 : ∀ i : Fin 96, connectRankValue (1056+i.val) = 0 → (1056+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 1056 48 48 connect_zero_root_b22 connect_zero_root_b23

private theorem connect_zero_root_n0_12 : ∀ i : Fin 96, connectRankValue (1152+i.val) = 0 → (1152+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 1152 48 48 connect_zero_root_b24 connect_zero_root_b25

private theorem connect_zero_root_n1_0 : ∀ i : Fin 192, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 96 96 connect_zero_root_n0_0 connect_zero_root_n0_1

private theorem connect_zero_root_n1_1 : ∀ i : Fin 192, connectRankValue (192+i.val) = 0 → (192+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 192 96 96 connect_zero_root_n0_2 connect_zero_root_n0_3

private theorem connect_zero_root_n1_2 : ∀ i : Fin 192, connectRankValue (384+i.val) = 0 → (384+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 384 96 96 connect_zero_root_n0_4 connect_zero_root_n0_5

private theorem connect_zero_root_n1_3 : ∀ i : Fin 192, connectRankValue (576+i.val) = 0 → (576+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 576 96 96 connect_zero_root_n0_6 connect_zero_root_n0_7

private theorem connect_zero_root_n1_4 : ∀ i : Fin 192, connectRankValue (768+i.val) = 0 → (768+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 768 96 96 connect_zero_root_n0_8 connect_zero_root_n0_9

private theorem connect_zero_root_n1_5 : ∀ i : Fin 192, connectRankValue (960+i.val) = 0 → (960+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 960 96 96 connect_zero_root_n0_10 connect_zero_root_n0_11

private theorem connect_zero_root_n1_6 : ∀ i : Fin 122, connectRankValue (1152+i.val) = 0 → (1152+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 1152 96 26 connect_zero_root_n0_12 connect_zero_root_b26

private theorem connect_zero_root_n2_0 : ∀ i : Fin 384, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 192 192 connect_zero_root_n1_0 connect_zero_root_n1_1

private theorem connect_zero_root_n2_1 : ∀ i : Fin 384, connectRankValue (384+i.val) = 0 → (384+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 384 192 192 connect_zero_root_n1_2 connect_zero_root_n1_3

private theorem connect_zero_root_n2_2 : ∀ i : Fin 384, connectRankValue (768+i.val) = 0 → (768+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 768 192 192 connect_zero_root_n1_4 connect_zero_root_n1_5

private theorem connect_zero_root_n3_0 : ∀ i : Fin 768, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 384 384 connect_zero_root_n2_0 connect_zero_root_n2_1

private theorem connect_zero_root_n3_1 : ∀ i : Fin 506, connectRankValue (768+i.val) = 0 → (768+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 768 384 122 connect_zero_root_n2_2 connect_zero_root_n1_6

private theorem connect_zero_root_n4_0 : ∀ i : Fin 1274, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 768 506 connect_zero_root_n3_0 connect_zero_root_n3_1

theorem connect_zero_root : ∀ i : Fin 1274, connectRankValue i.val = 0 → i.val = 0 := by
  simpa only [Nat.zero_add] using connect_zero_root_n4_0

end PlanarHom.ColoringMacroFaces.CrossFramed
