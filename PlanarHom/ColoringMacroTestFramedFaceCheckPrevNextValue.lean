import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem prev_next_value_b0 : ∀ i : Fin 48, prevValue (nextValue (0+i.val)) = (0+i.val) := by decide +kernel

private theorem prev_next_value_b1 : ∀ i : Fin 48, prevValue (nextValue (48+i.val)) = (48+i.val) := by decide +kernel

private theorem prev_next_value_b2 : ∀ i : Fin 48, prevValue (nextValue (96+i.val)) = (96+i.val) := by decide +kernel

private theorem prev_next_value_b3 : ∀ i : Fin 48, prevValue (nextValue (144+i.val)) = (144+i.val) := by decide +kernel

private theorem prev_next_value_b4 : ∀ i : Fin 48, prevValue (nextValue (192+i.val)) = (192+i.val) := by decide +kernel

private theorem prev_next_value_b5 : ∀ i : Fin 48, prevValue (nextValue (240+i.val)) = (240+i.val) := by decide +kernel

private theorem prev_next_value_b6 : ∀ i : Fin 48, prevValue (nextValue (288+i.val)) = (288+i.val) := by decide +kernel

private theorem prev_next_value_b7 : ∀ i : Fin 48, prevValue (nextValue (336+i.val)) = (336+i.val) := by decide +kernel

private theorem prev_next_value_b8 : ∀ i : Fin 48, prevValue (nextValue (384+i.val)) = (384+i.val) := by decide +kernel

private theorem prev_next_value_b9 : ∀ i : Fin 48, prevValue (nextValue (432+i.val)) = (432+i.val) := by decide +kernel

private theorem prev_next_value_b10 : ∀ i : Fin 48, prevValue (nextValue (480+i.val)) = (480+i.val) := by decide +kernel

private theorem prev_next_value_b11 : ∀ i : Fin 42, prevValue (nextValue (528+i.val)) = (528+i.val) := by decide +kernel

private theorem prev_next_value_n0_0 : ∀ i : Fin 96, prevValue (nextValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 0 48 48 prev_next_value_b0 prev_next_value_b1

private theorem prev_next_value_n0_1 : ∀ i : Fin 96, prevValue (nextValue (96+i.val)) = (96+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 96 48 48 prev_next_value_b2 prev_next_value_b3

private theorem prev_next_value_n0_2 : ∀ i : Fin 96, prevValue (nextValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 192 48 48 prev_next_value_b4 prev_next_value_b5

private theorem prev_next_value_n0_3 : ∀ i : Fin 96, prevValue (nextValue (288+i.val)) = (288+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 288 48 48 prev_next_value_b6 prev_next_value_b7

private theorem prev_next_value_n0_4 : ∀ i : Fin 96, prevValue (nextValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 384 48 48 prev_next_value_b8 prev_next_value_b9

private theorem prev_next_value_n0_5 : ∀ i : Fin 90, prevValue (nextValue (480+i.val)) = (480+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 480 48 42 prev_next_value_b10 prev_next_value_b11

private theorem prev_next_value_n1_0 : ∀ i : Fin 192, prevValue (nextValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 0 96 96 prev_next_value_n0_0 prev_next_value_n0_1

private theorem prev_next_value_n1_1 : ∀ i : Fin 192, prevValue (nextValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 192 96 96 prev_next_value_n0_2 prev_next_value_n0_3

private theorem prev_next_value_n1_2 : ∀ i : Fin 186, prevValue (nextValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 384 96 90 prev_next_value_n0_4 prev_next_value_n0_5

private theorem prev_next_value_n2_0 : ∀ i : Fin 384, prevValue (nextValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 0 192 192 prev_next_value_n1_0 prev_next_value_n1_1

private theorem prev_next_value_n3_0 : ∀ i : Fin 570, prevValue (nextValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => prevValue (nextValue i) = i) 0 384 186 prev_next_value_n2_0 prev_next_value_n1_2

theorem prev_next_value : ∀ i : Fin 570, prevValue (nextValue i.val) = i.val := by
  simpa only [Nat.zero_add] using prev_next_value_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
