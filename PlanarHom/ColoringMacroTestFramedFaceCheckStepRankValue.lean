import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem step_rank_value_b0 : ∀ i : Fin 48, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) := by decide +kernel

private theorem step_rank_value_b1 : ∀ i : Fin 48, 0 < rankValue (48+i.val) → rankValue (nextValue (48+i.val)) + 1 = rankValue (48+i.val) := by decide +kernel

private theorem step_rank_value_b2 : ∀ i : Fin 48, 0 < rankValue (96+i.val) → rankValue (nextValue (96+i.val)) + 1 = rankValue (96+i.val) := by decide +kernel

private theorem step_rank_value_b3 : ∀ i : Fin 48, 0 < rankValue (144+i.val) → rankValue (nextValue (144+i.val)) + 1 = rankValue (144+i.val) := by decide +kernel

private theorem step_rank_value_b4 : ∀ i : Fin 48, 0 < rankValue (192+i.val) → rankValue (nextValue (192+i.val)) + 1 = rankValue (192+i.val) := by decide +kernel

private theorem step_rank_value_b5 : ∀ i : Fin 48, 0 < rankValue (240+i.val) → rankValue (nextValue (240+i.val)) + 1 = rankValue (240+i.val) := by decide +kernel

private theorem step_rank_value_b6 : ∀ i : Fin 48, 0 < rankValue (288+i.val) → rankValue (nextValue (288+i.val)) + 1 = rankValue (288+i.val) := by decide +kernel

private theorem step_rank_value_b7 : ∀ i : Fin 48, 0 < rankValue (336+i.val) → rankValue (nextValue (336+i.val)) + 1 = rankValue (336+i.val) := by decide +kernel

private theorem step_rank_value_b8 : ∀ i : Fin 48, 0 < rankValue (384+i.val) → rankValue (nextValue (384+i.val)) + 1 = rankValue (384+i.val) := by decide +kernel

private theorem step_rank_value_b9 : ∀ i : Fin 48, 0 < rankValue (432+i.val) → rankValue (nextValue (432+i.val)) + 1 = rankValue (432+i.val) := by decide +kernel

private theorem step_rank_value_b10 : ∀ i : Fin 48, 0 < rankValue (480+i.val) → rankValue (nextValue (480+i.val)) + 1 = rankValue (480+i.val) := by decide +kernel

private theorem step_rank_value_b11 : ∀ i : Fin 42, 0 < rankValue (528+i.val) → rankValue (nextValue (528+i.val)) + 1 = rankValue (528+i.val) := by decide +kernel

private theorem step_rank_value_n0_0 : ∀ i : Fin 96, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 48 48 step_rank_value_b0 step_rank_value_b1

private theorem step_rank_value_n0_1 : ∀ i : Fin 96, 0 < rankValue (96+i.val) → rankValue (nextValue (96+i.val)) + 1 = rankValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 96 48 48 step_rank_value_b2 step_rank_value_b3

private theorem step_rank_value_n0_2 : ∀ i : Fin 96, 0 < rankValue (192+i.val) → rankValue (nextValue (192+i.val)) + 1 = rankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 192 48 48 step_rank_value_b4 step_rank_value_b5

private theorem step_rank_value_n0_3 : ∀ i : Fin 96, 0 < rankValue (288+i.val) → rankValue (nextValue (288+i.val)) + 1 = rankValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 288 48 48 step_rank_value_b6 step_rank_value_b7

private theorem step_rank_value_n0_4 : ∀ i : Fin 96, 0 < rankValue (384+i.val) → rankValue (nextValue (384+i.val)) + 1 = rankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 384 48 48 step_rank_value_b8 step_rank_value_b9

private theorem step_rank_value_n0_5 : ∀ i : Fin 90, 0 < rankValue (480+i.val) → rankValue (nextValue (480+i.val)) + 1 = rankValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 480 48 42 step_rank_value_b10 step_rank_value_b11

private theorem step_rank_value_n1_0 : ∀ i : Fin 192, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 96 96 step_rank_value_n0_0 step_rank_value_n0_1

private theorem step_rank_value_n1_1 : ∀ i : Fin 192, 0 < rankValue (192+i.val) → rankValue (nextValue (192+i.val)) + 1 = rankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 192 96 96 step_rank_value_n0_2 step_rank_value_n0_3

private theorem step_rank_value_n1_2 : ∀ i : Fin 186, 0 < rankValue (384+i.val) → rankValue (nextValue (384+i.val)) + 1 = rankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 384 96 90 step_rank_value_n0_4 step_rank_value_n0_5

private theorem step_rank_value_n2_0 : ∀ i : Fin 384, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 192 192 step_rank_value_n1_0 step_rank_value_n1_1

private theorem step_rank_value_n3_0 : ∀ i : Fin 570, 0 < rankValue (0+i.val) → rankValue (nextValue (0+i.val)) + 1 = rankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < rankValue i → rankValue (nextValue i) + 1 = rankValue i) 0 384 186 step_rank_value_n2_0 step_rank_value_n1_2

theorem step_rank_value : ∀ i : Fin 570, 0 < rankValue i.val → rankValue (nextValue i.val) + 1 = rankValue i.val := by
  simpa only [Nat.zero_add] using step_rank_value_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
