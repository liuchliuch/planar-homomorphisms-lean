import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem prevBound_b0 : ∀ i : Fin 48, prevValue (0+i.val) < 570 := by decide +kernel

private theorem prevBound_b1 : ∀ i : Fin 48, prevValue (48+i.val) < 570 := by decide +kernel

private theorem prevBound_b2 : ∀ i : Fin 48, prevValue (96+i.val) < 570 := by decide +kernel

private theorem prevBound_b3 : ∀ i : Fin 48, prevValue (144+i.val) < 570 := by decide +kernel

private theorem prevBound_b4 : ∀ i : Fin 48, prevValue (192+i.val) < 570 := by decide +kernel

private theorem prevBound_b5 : ∀ i : Fin 48, prevValue (240+i.val) < 570 := by decide +kernel

private theorem prevBound_b6 : ∀ i : Fin 48, prevValue (288+i.val) < 570 := by decide +kernel

private theorem prevBound_b7 : ∀ i : Fin 48, prevValue (336+i.val) < 570 := by decide +kernel

private theorem prevBound_b8 : ∀ i : Fin 48, prevValue (384+i.val) < 570 := by decide +kernel

private theorem prevBound_b9 : ∀ i : Fin 48, prevValue (432+i.val) < 570 := by decide +kernel

private theorem prevBound_b10 : ∀ i : Fin 48, prevValue (480+i.val) < 570 := by decide +kernel

private theorem prevBound_b11 : ∀ i : Fin 42, prevValue (528+i.val) < 570 := by decide +kernel

private theorem prevBound_n0_0 : ∀ i : Fin 96, prevValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 0 48 48 prevBound_b0 prevBound_b1

private theorem prevBound_n0_1 : ∀ i : Fin 96, prevValue (96+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 96 48 48 prevBound_b2 prevBound_b3

private theorem prevBound_n0_2 : ∀ i : Fin 96, prevValue (192+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 192 48 48 prevBound_b4 prevBound_b5

private theorem prevBound_n0_3 : ∀ i : Fin 96, prevValue (288+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 288 48 48 prevBound_b6 prevBound_b7

private theorem prevBound_n0_4 : ∀ i : Fin 96, prevValue (384+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 384 48 48 prevBound_b8 prevBound_b9

private theorem prevBound_n0_5 : ∀ i : Fin 90, prevValue (480+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 480 48 42 prevBound_b10 prevBound_b11

private theorem prevBound_n1_0 : ∀ i : Fin 192, prevValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 0 96 96 prevBound_n0_0 prevBound_n0_1

private theorem prevBound_n1_1 : ∀ i : Fin 192, prevValue (192+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 192 96 96 prevBound_n0_2 prevBound_n0_3

private theorem prevBound_n1_2 : ∀ i : Fin 186, prevValue (384+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 384 96 90 prevBound_n0_4 prevBound_n0_5

private theorem prevBound_n2_0 : ∀ i : Fin 384, prevValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 0 192 192 prevBound_n1_0 prevBound_n1_1

private theorem prevBound_n3_0 : ∀ i : Fin 570, prevValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => prevValue i < 570) 0 384 186 prevBound_n2_0 prevBound_n1_2

theorem prevBound : ∀ i : Fin 570, prevValue i.val < 570 := by
  simpa only [Nat.zero_add] using prevBound_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
