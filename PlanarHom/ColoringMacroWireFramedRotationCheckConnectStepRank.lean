import PlanarHom.ColoringMacroWireFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
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

private theorem connect_step_rank_b11 : ∀ i : Fin 6, 0 < connectRankValue (528+i.val) → connectRankValue (parentValue (528+i.val)) < connectRankValue (528+i.val) := by decide +kernel

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

private theorem connect_step_rank_n0_5 : ∀ i : Fin 54, 0 < connectRankValue (480+i.val) → connectRankValue (parentValue (480+i.val)) < connectRankValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 480 48 6 connect_step_rank_b10 connect_step_rank_b11

private theorem connect_step_rank_n1_0 : ∀ i : Fin 192, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 96 96 connect_step_rank_n0_0 connect_step_rank_n0_1

private theorem connect_step_rank_n1_1 : ∀ i : Fin 192, 0 < connectRankValue (192+i.val) → connectRankValue (parentValue (192+i.val)) < connectRankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 192 96 96 connect_step_rank_n0_2 connect_step_rank_n0_3

private theorem connect_step_rank_n1_2 : ∀ i : Fin 150, 0 < connectRankValue (384+i.val) → connectRankValue (parentValue (384+i.val)) < connectRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 384 96 54 connect_step_rank_n0_4 connect_step_rank_n0_5

private theorem connect_step_rank_n2_0 : ∀ i : Fin 384, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 192 192 connect_step_rank_n1_0 connect_step_rank_n1_1

private theorem connect_step_rank_n3_0 : ∀ i : Fin 534, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 384 150 connect_step_rank_n2_0 connect_step_rank_n1_2

theorem connect_step_rank : ∀ i : Fin 534, 0 < connectRankValue i.val → connectRankValue (parentValue i.val) < connectRankValue i.val := by
  simpa only [Nat.zero_add] using connect_step_rank_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
