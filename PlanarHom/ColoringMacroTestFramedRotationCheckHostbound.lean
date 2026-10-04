import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem hostBound_b0 : ∀ i : Fin 48, hostValue (0+i.val) < 118 := by decide +kernel

private theorem hostBound_b1 : ∀ i : Fin 48, hostValue (48+i.val) < 118 := by decide +kernel

private theorem hostBound_b2 : ∀ i : Fin 48, hostValue (96+i.val) < 118 := by decide +kernel

private theorem hostBound_b3 : ∀ i : Fin 48, hostValue (144+i.val) < 118 := by decide +kernel

private theorem hostBound_b4 : ∀ i : Fin 48, hostValue (192+i.val) < 118 := by decide +kernel

private theorem hostBound_b5 : ∀ i : Fin 48, hostValue (240+i.val) < 118 := by decide +kernel

private theorem hostBound_b6 : ∀ i : Fin 48, hostValue (288+i.val) < 118 := by decide +kernel

private theorem hostBound_b7 : ∀ i : Fin 48, hostValue (336+i.val) < 118 := by decide +kernel

private theorem hostBound_b8 : ∀ i : Fin 48, hostValue (384+i.val) < 118 := by decide +kernel

private theorem hostBound_b9 : ∀ i : Fin 48, hostValue (432+i.val) < 118 := by decide +kernel

private theorem hostBound_b10 : ∀ i : Fin 48, hostValue (480+i.val) < 118 := by decide +kernel

private theorem hostBound_b11 : ∀ i : Fin 42, hostValue (528+i.val) < 118 := by decide +kernel

private theorem hostBound_n0_0 : ∀ i : Fin 96, hostValue (0+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 0 48 48 hostBound_b0 hostBound_b1

private theorem hostBound_n0_1 : ∀ i : Fin 96, hostValue (96+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 96 48 48 hostBound_b2 hostBound_b3

private theorem hostBound_n0_2 : ∀ i : Fin 96, hostValue (192+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 192 48 48 hostBound_b4 hostBound_b5

private theorem hostBound_n0_3 : ∀ i : Fin 96, hostValue (288+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 288 48 48 hostBound_b6 hostBound_b7

private theorem hostBound_n0_4 : ∀ i : Fin 96, hostValue (384+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 384 48 48 hostBound_b8 hostBound_b9

private theorem hostBound_n0_5 : ∀ i : Fin 90, hostValue (480+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 480 48 42 hostBound_b10 hostBound_b11

private theorem hostBound_n1_0 : ∀ i : Fin 192, hostValue (0+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 0 96 96 hostBound_n0_0 hostBound_n0_1

private theorem hostBound_n1_1 : ∀ i : Fin 192, hostValue (192+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 192 96 96 hostBound_n0_2 hostBound_n0_3

private theorem hostBound_n1_2 : ∀ i : Fin 186, hostValue (384+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 384 96 90 hostBound_n0_4 hostBound_n0_5

private theorem hostBound_n2_0 : ∀ i : Fin 384, hostValue (0+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 0 192 192 hostBound_n1_0 hostBound_n1_1

private theorem hostBound_n3_0 : ∀ i : Fin 570, hostValue (0+i.val) < 118 :=
  FiniteIntervalCheck.append (fun i => hostValue i < 118) 0 384 186 hostBound_n2_0 hostBound_n1_2

theorem hostBound : ∀ i : Fin 570, hostValue i.val < 118 := by
  simpa only [Nat.zero_add] using hostBound_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
