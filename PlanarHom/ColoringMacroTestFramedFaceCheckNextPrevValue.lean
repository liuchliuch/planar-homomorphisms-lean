import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem next_prev_value_b0 : ∀ i : Fin 48, nextValue (prevValue (0+i.val)) = (0+i.val) := by decide +kernel

private theorem next_prev_value_b1 : ∀ i : Fin 48, nextValue (prevValue (48+i.val)) = (48+i.val) := by decide +kernel

private theorem next_prev_value_b2 : ∀ i : Fin 48, nextValue (prevValue (96+i.val)) = (96+i.val) := by decide +kernel

private theorem next_prev_value_b3 : ∀ i : Fin 48, nextValue (prevValue (144+i.val)) = (144+i.val) := by decide +kernel

private theorem next_prev_value_b4 : ∀ i : Fin 48, nextValue (prevValue (192+i.val)) = (192+i.val) := by decide +kernel

private theorem next_prev_value_b5 : ∀ i : Fin 48, nextValue (prevValue (240+i.val)) = (240+i.val) := by decide +kernel

private theorem next_prev_value_b6 : ∀ i : Fin 48, nextValue (prevValue (288+i.val)) = (288+i.val) := by decide +kernel

private theorem next_prev_value_b7 : ∀ i : Fin 48, nextValue (prevValue (336+i.val)) = (336+i.val) := by decide +kernel

private theorem next_prev_value_b8 : ∀ i : Fin 48, nextValue (prevValue (384+i.val)) = (384+i.val) := by decide +kernel

private theorem next_prev_value_b9 : ∀ i : Fin 48, nextValue (prevValue (432+i.val)) = (432+i.val) := by decide +kernel

private theorem next_prev_value_b10 : ∀ i : Fin 48, nextValue (prevValue (480+i.val)) = (480+i.val) := by decide +kernel

private theorem next_prev_value_b11 : ∀ i : Fin 42, nextValue (prevValue (528+i.val)) = (528+i.val) := by decide +kernel

private theorem next_prev_value_n0_0 : ∀ i : Fin 96, nextValue (prevValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 0 48 48 next_prev_value_b0 next_prev_value_b1

private theorem next_prev_value_n0_1 : ∀ i : Fin 96, nextValue (prevValue (96+i.val)) = (96+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 96 48 48 next_prev_value_b2 next_prev_value_b3

private theorem next_prev_value_n0_2 : ∀ i : Fin 96, nextValue (prevValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 192 48 48 next_prev_value_b4 next_prev_value_b5

private theorem next_prev_value_n0_3 : ∀ i : Fin 96, nextValue (prevValue (288+i.val)) = (288+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 288 48 48 next_prev_value_b6 next_prev_value_b7

private theorem next_prev_value_n0_4 : ∀ i : Fin 96, nextValue (prevValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 384 48 48 next_prev_value_b8 next_prev_value_b9

private theorem next_prev_value_n0_5 : ∀ i : Fin 90, nextValue (prevValue (480+i.val)) = (480+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 480 48 42 next_prev_value_b10 next_prev_value_b11

private theorem next_prev_value_n1_0 : ∀ i : Fin 192, nextValue (prevValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 0 96 96 next_prev_value_n0_0 next_prev_value_n0_1

private theorem next_prev_value_n1_1 : ∀ i : Fin 192, nextValue (prevValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 192 96 96 next_prev_value_n0_2 next_prev_value_n0_3

private theorem next_prev_value_n1_2 : ∀ i : Fin 186, nextValue (prevValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 384 96 90 next_prev_value_n0_4 next_prev_value_n0_5

private theorem next_prev_value_n2_0 : ∀ i : Fin 384, nextValue (prevValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 0 192 192 next_prev_value_n1_0 next_prev_value_n1_1

private theorem next_prev_value_n3_0 : ∀ i : Fin 570, nextValue (prevValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => nextValue (prevValue i) = i) 0 384 186 next_prev_value_n2_0 next_prev_value_n1_2

theorem next_prev_value : ∀ i : Fin 570, nextValue (prevValue i.val) = i.val := by
  simpa only [Nat.zero_add] using next_prev_value_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
