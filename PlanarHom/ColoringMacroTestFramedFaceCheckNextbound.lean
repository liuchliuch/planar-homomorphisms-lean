import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem nextBound_b0 : ∀ i : Fin 48, nextValue (0+i.val) < 570 := by decide +kernel

private theorem nextBound_b1 : ∀ i : Fin 48, nextValue (48+i.val) < 570 := by decide +kernel

private theorem nextBound_b2 : ∀ i : Fin 48, nextValue (96+i.val) < 570 := by decide +kernel

private theorem nextBound_b3 : ∀ i : Fin 48, nextValue (144+i.val) < 570 := by decide +kernel

private theorem nextBound_b4 : ∀ i : Fin 48, nextValue (192+i.val) < 570 := by decide +kernel

private theorem nextBound_b5 : ∀ i : Fin 48, nextValue (240+i.val) < 570 := by decide +kernel

private theorem nextBound_b6 : ∀ i : Fin 48, nextValue (288+i.val) < 570 := by decide +kernel

private theorem nextBound_b7 : ∀ i : Fin 48, nextValue (336+i.val) < 570 := by decide +kernel

private theorem nextBound_b8 : ∀ i : Fin 48, nextValue (384+i.val) < 570 := by decide +kernel

private theorem nextBound_b9 : ∀ i : Fin 48, nextValue (432+i.val) < 570 := by decide +kernel

private theorem nextBound_b10 : ∀ i : Fin 48, nextValue (480+i.val) < 570 := by decide +kernel

private theorem nextBound_b11 : ∀ i : Fin 42, nextValue (528+i.val) < 570 := by decide +kernel

private theorem nextBound_n0_0 : ∀ i : Fin 96, nextValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 0 48 48 nextBound_b0 nextBound_b1

private theorem nextBound_n0_1 : ∀ i : Fin 96, nextValue (96+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 96 48 48 nextBound_b2 nextBound_b3

private theorem nextBound_n0_2 : ∀ i : Fin 96, nextValue (192+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 192 48 48 nextBound_b4 nextBound_b5

private theorem nextBound_n0_3 : ∀ i : Fin 96, nextValue (288+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 288 48 48 nextBound_b6 nextBound_b7

private theorem nextBound_n0_4 : ∀ i : Fin 96, nextValue (384+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 384 48 48 nextBound_b8 nextBound_b9

private theorem nextBound_n0_5 : ∀ i : Fin 90, nextValue (480+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 480 48 42 nextBound_b10 nextBound_b11

private theorem nextBound_n1_0 : ∀ i : Fin 192, nextValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 0 96 96 nextBound_n0_0 nextBound_n0_1

private theorem nextBound_n1_1 : ∀ i : Fin 192, nextValue (192+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 192 96 96 nextBound_n0_2 nextBound_n0_3

private theorem nextBound_n1_2 : ∀ i : Fin 186, nextValue (384+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 384 96 90 nextBound_n0_4 nextBound_n0_5

private theorem nextBound_n2_0 : ∀ i : Fin 384, nextValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 0 192 192 nextBound_n1_0 nextBound_n1_1

private theorem nextBound_n3_0 : ∀ i : Fin 570, nextValue (0+i.val) < 570 :=
  FiniteIntervalCheck.append (fun i => nextValue i < 570) 0 384 186 nextBound_n2_0 nextBound_n1_2

theorem nextBound : ∀ i : Fin 570, nextValue i.val < 570 := by
  simpa only [Nat.zero_add] using nextBound_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
