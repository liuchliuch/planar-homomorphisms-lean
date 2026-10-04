import PlanarHom.ColoringMacroWireFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
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

private theorem connect_zero_root_b11 : ∀ i : Fin 6, connectRankValue (528+i.val) = 0 → (528+i.val) = 0 := by decide +kernel

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

private theorem connect_zero_root_n0_5 : ∀ i : Fin 54, connectRankValue (480+i.val) = 0 → (480+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 480 48 6 connect_zero_root_b10 connect_zero_root_b11

private theorem connect_zero_root_n1_0 : ∀ i : Fin 192, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 96 96 connect_zero_root_n0_0 connect_zero_root_n0_1

private theorem connect_zero_root_n1_1 : ∀ i : Fin 192, connectRankValue (192+i.val) = 0 → (192+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 192 96 96 connect_zero_root_n0_2 connect_zero_root_n0_3

private theorem connect_zero_root_n1_2 : ∀ i : Fin 150, connectRankValue (384+i.val) = 0 → (384+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 384 96 54 connect_zero_root_n0_4 connect_zero_root_n0_5

private theorem connect_zero_root_n2_0 : ∀ i : Fin 384, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 192 192 connect_zero_root_n1_0 connect_zero_root_n1_1

private theorem connect_zero_root_n3_0 : ∀ i : Fin 534, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 384 150 connect_zero_root_n2_0 connect_zero_root_n1_2

theorem connect_zero_root : ∀ i : Fin 534, connectRankValue i.val = 0 → i.val = 0 := by
  simpa only [Nat.zero_add] using connect_zero_root_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
