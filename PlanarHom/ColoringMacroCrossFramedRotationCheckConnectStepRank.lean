import PlanarHom.ColoringMacroCrossFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.CrossFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem connect_step_rank_b0 : ∀ i : Fin 48, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) := by decide +kernel

private theorem connect_step_rank_b1 : ∀ i : Fin 48, 0 < connectRankValue (48+i.val) → connectRankValue (parentValue (48+i.val)) < connectRankValue (48+i.val) := by decide +kernel

private theorem connect_step_rank_b2 : ∀ i : Fin 48, 0 < connectRankValue (96+i.val) → connectRankValue (parentValue (96+i.val)) < connectRankValue (96+i.val) := by decide +kernel

private theorem connect_step_rank_b3 : ∀ i : Fin 48, 0 < connectRankValue (144+i.val) → connectRankValue (parentValue (144+i.val)) < connectRankValue (144+i.val) := by decide +kernel

private theorem connect_step_rank_b4 : ∀ i : Fin 48, 0 < connectRankValue (192+i.val) → connectRankValue (parentValue (192+i.val)) < connectRankValue (192+i.val) := by decide +kernel

private theorem connect_step_rank_b5 : ∀ i : Fin 48, 0 < connectRankValue (240+i.val) → connectRankValue (parentValue (240+i.val)) < connectRankValue (240+i.val) := by decide +kernel

private theorem connect_step_rank_b6 : ∀ i : Fin 48, 0 < connectRankValue (288+i.val) → connectRankValue (parentValue (288+i.val)) < connectRankValue (288+i.val) := by decide +kernel

private theorem connect_step_rank_b7 : ∀ i : Fin 48, 0 < connectRankValue (336+i.val) → connectRankValue (parentValue (336+i.val)) < connectRankValue (336+i.val) := by decide +kernel

private theorem connect_step_rank_b8 : ∀ i : Fin 48, 0 < connectRankValue (384+i.val) → connectRankValue (parentValue (384+i.val)) < connectRankValue (384+i.val) := by decide +kernel

private theorem connect_step_rank_b9 : ∀ i : Fin 48, 0 < connectRankValue (432+i.val) → connectRankValue (parentValue (432+i.val)) < connectRankValue (432+i.val) := by decide +kernel

private theorem connect_step_rank_b10 : ∀ i : Fin 48, 0 < connectRankValue (480+i.val) → connectRankValue (parentValue (480+i.val)) < connectRankValue (480+i.val) := by decide +kernel

private theorem connect_step_rank_b11 : ∀ i : Fin 48, 0 < connectRankValue (528+i.val) → connectRankValue (parentValue (528+i.val)) < connectRankValue (528+i.val) := by decide +kernel

private theorem connect_step_rank_b12 : ∀ i : Fin 48, 0 < connectRankValue (576+i.val) → connectRankValue (parentValue (576+i.val)) < connectRankValue (576+i.val) := by decide +kernel

private theorem connect_step_rank_b13 : ∀ i : Fin 48, 0 < connectRankValue (624+i.val) → connectRankValue (parentValue (624+i.val)) < connectRankValue (624+i.val) := by decide +kernel

private theorem connect_step_rank_b14 : ∀ i : Fin 48, 0 < connectRankValue (672+i.val) → connectRankValue (parentValue (672+i.val)) < connectRankValue (672+i.val) := by decide +kernel

private theorem connect_step_rank_b15 : ∀ i : Fin 48, 0 < connectRankValue (720+i.val) → connectRankValue (parentValue (720+i.val)) < connectRankValue (720+i.val) := by decide +kernel

private theorem connect_step_rank_b16 : ∀ i : Fin 48, 0 < connectRankValue (768+i.val) → connectRankValue (parentValue (768+i.val)) < connectRankValue (768+i.val) := by decide +kernel

private theorem connect_step_rank_b17 : ∀ i : Fin 48, 0 < connectRankValue (816+i.val) → connectRankValue (parentValue (816+i.val)) < connectRankValue (816+i.val) := by decide +kernel

private theorem connect_step_rank_b18 : ∀ i : Fin 48, 0 < connectRankValue (864+i.val) → connectRankValue (parentValue (864+i.val)) < connectRankValue (864+i.val) := by decide +kernel

private theorem connect_step_rank_b19 : ∀ i : Fin 48, 0 < connectRankValue (912+i.val) → connectRankValue (parentValue (912+i.val)) < connectRankValue (912+i.val) := by decide +kernel

private theorem connect_step_rank_b20 : ∀ i : Fin 48, 0 < connectRankValue (960+i.val) → connectRankValue (parentValue (960+i.val)) < connectRankValue (960+i.val) := by decide +kernel

private theorem connect_step_rank_b21 : ∀ i : Fin 48, 0 < connectRankValue (1008+i.val) → connectRankValue (parentValue (1008+i.val)) < connectRankValue (1008+i.val) := by decide +kernel

private theorem connect_step_rank_b22 : ∀ i : Fin 48, 0 < connectRankValue (1056+i.val) → connectRankValue (parentValue (1056+i.val)) < connectRankValue (1056+i.val) := by decide +kernel

private theorem connect_step_rank_b23 : ∀ i : Fin 48, 0 < connectRankValue (1104+i.val) → connectRankValue (parentValue (1104+i.val)) < connectRankValue (1104+i.val) := by decide +kernel

private theorem connect_step_rank_b24 : ∀ i : Fin 48, 0 < connectRankValue (1152+i.val) → connectRankValue (parentValue (1152+i.val)) < connectRankValue (1152+i.val) := by decide +kernel

private theorem connect_step_rank_b25 : ∀ i : Fin 48, 0 < connectRankValue (1200+i.val) → connectRankValue (parentValue (1200+i.val)) < connectRankValue (1200+i.val) := by decide +kernel

private theorem connect_step_rank_b26 : ∀ i : Fin 26, 0 < connectRankValue (1248+i.val) → connectRankValue (parentValue (1248+i.val)) < connectRankValue (1248+i.val) := by decide +kernel

private theorem connect_step_rank_n0_0 : ∀ i : Fin 96, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 48 48 connect_step_rank_b0 connect_step_rank_b1

private theorem connect_step_rank_n0_1 : ∀ i : Fin 96, 0 < connectRankValue (96+i.val) → connectRankValue (parentValue (96+i.val)) < connectRankValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 96 48 48 connect_step_rank_b2 connect_step_rank_b3

private theorem connect_step_rank_n0_2 : ∀ i : Fin 96, 0 < connectRankValue (192+i.val) → connectRankValue (parentValue (192+i.val)) < connectRankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 192 48 48 connect_step_rank_b4 connect_step_rank_b5

private theorem connect_step_rank_n0_3 : ∀ i : Fin 96, 0 < connectRankValue (288+i.val) → connectRankValue (parentValue (288+i.val)) < connectRankValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 288 48 48 connect_step_rank_b6 connect_step_rank_b7

private theorem connect_step_rank_n0_4 : ∀ i : Fin 96, 0 < connectRankValue (384+i.val) → connectRankValue (parentValue (384+i.val)) < connectRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 384 48 48 connect_step_rank_b8 connect_step_rank_b9

private theorem connect_step_rank_n0_5 : ∀ i : Fin 96, 0 < connectRankValue (480+i.val) → connectRankValue (parentValue (480+i.val)) < connectRankValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 480 48 48 connect_step_rank_b10 connect_step_rank_b11

private theorem connect_step_rank_n0_6 : ∀ i : Fin 96, 0 < connectRankValue (576+i.val) → connectRankValue (parentValue (576+i.val)) < connectRankValue (576+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 576 48 48 connect_step_rank_b12 connect_step_rank_b13

private theorem connect_step_rank_n0_7 : ∀ i : Fin 96, 0 < connectRankValue (672+i.val) → connectRankValue (parentValue (672+i.val)) < connectRankValue (672+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 672 48 48 connect_step_rank_b14 connect_step_rank_b15

private theorem connect_step_rank_n0_8 : ∀ i : Fin 96, 0 < connectRankValue (768+i.val) → connectRankValue (parentValue (768+i.val)) < connectRankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 768 48 48 connect_step_rank_b16 connect_step_rank_b17

private theorem connect_step_rank_n0_9 : ∀ i : Fin 96, 0 < connectRankValue (864+i.val) → connectRankValue (parentValue (864+i.val)) < connectRankValue (864+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 864 48 48 connect_step_rank_b18 connect_step_rank_b19

private theorem connect_step_rank_n0_10 : ∀ i : Fin 96, 0 < connectRankValue (960+i.val) → connectRankValue (parentValue (960+i.val)) < connectRankValue (960+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 960 48 48 connect_step_rank_b20 connect_step_rank_b21

private theorem connect_step_rank_n0_11 : ∀ i : Fin 96, 0 < connectRankValue (1056+i.val) → connectRankValue (parentValue (1056+i.val)) < connectRankValue (1056+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 1056 48 48 connect_step_rank_b22 connect_step_rank_b23

private theorem connect_step_rank_n0_12 : ∀ i : Fin 96, 0 < connectRankValue (1152+i.val) → connectRankValue (parentValue (1152+i.val)) < connectRankValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 1152 48 48 connect_step_rank_b24 connect_step_rank_b25

private theorem connect_step_rank_n1_0 : ∀ i : Fin 192, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 96 96 connect_step_rank_n0_0 connect_step_rank_n0_1

private theorem connect_step_rank_n1_1 : ∀ i : Fin 192, 0 < connectRankValue (192+i.val) → connectRankValue (parentValue (192+i.val)) < connectRankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 192 96 96 connect_step_rank_n0_2 connect_step_rank_n0_3

private theorem connect_step_rank_n1_2 : ∀ i : Fin 192, 0 < connectRankValue (384+i.val) → connectRankValue (parentValue (384+i.val)) < connectRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 384 96 96 connect_step_rank_n0_4 connect_step_rank_n0_5

private theorem connect_step_rank_n1_3 : ∀ i : Fin 192, 0 < connectRankValue (576+i.val) → connectRankValue (parentValue (576+i.val)) < connectRankValue (576+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 576 96 96 connect_step_rank_n0_6 connect_step_rank_n0_7

private theorem connect_step_rank_n1_4 : ∀ i : Fin 192, 0 < connectRankValue (768+i.val) → connectRankValue (parentValue (768+i.val)) < connectRankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 768 96 96 connect_step_rank_n0_8 connect_step_rank_n0_9

private theorem connect_step_rank_n1_5 : ∀ i : Fin 192, 0 < connectRankValue (960+i.val) → connectRankValue (parentValue (960+i.val)) < connectRankValue (960+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 960 96 96 connect_step_rank_n0_10 connect_step_rank_n0_11

private theorem connect_step_rank_n1_6 : ∀ i : Fin 122, 0 < connectRankValue (1152+i.val) → connectRankValue (parentValue (1152+i.val)) < connectRankValue (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 1152 96 26 connect_step_rank_n0_12 connect_step_rank_b26

private theorem connect_step_rank_n2_0 : ∀ i : Fin 384, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 192 192 connect_step_rank_n1_0 connect_step_rank_n1_1

private theorem connect_step_rank_n2_1 : ∀ i : Fin 384, 0 < connectRankValue (384+i.val) → connectRankValue (parentValue (384+i.val)) < connectRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 384 192 192 connect_step_rank_n1_2 connect_step_rank_n1_3

private theorem connect_step_rank_n2_2 : ∀ i : Fin 384, 0 < connectRankValue (768+i.val) → connectRankValue (parentValue (768+i.val)) < connectRankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 768 192 192 connect_step_rank_n1_4 connect_step_rank_n1_5

private theorem connect_step_rank_n3_0 : ∀ i : Fin 768, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 384 384 connect_step_rank_n2_0 connect_step_rank_n2_1

private theorem connect_step_rank_n3_1 : ∀ i : Fin 506, 0 < connectRankValue (768+i.val) → connectRankValue (parentValue (768+i.val)) < connectRankValue (768+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 768 384 122 connect_step_rank_n2_2 connect_step_rank_n1_6

private theorem connect_step_rank_n4_0 : ∀ i : Fin 1274, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 768 506 connect_step_rank_n3_0 connect_step_rank_n3_1

theorem connect_step_rank : ∀ i : Fin 1274, 0 < connectRankValue i.val → connectRankValue (parentValue i.val) < connectRankValue i.val := by
  simpa only [Nat.zero_add] using connect_step_rank_n4_0

end PlanarHom.ColoringMacroFaces.CrossFramed
