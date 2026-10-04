import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem step_label_value_b0 : ∀ i : Fin 48, labelValue (nextValue (0+i.val)) = labelValue (0+i.val) := by decide +kernel

private theorem step_label_value_b1 : ∀ i : Fin 48, labelValue (nextValue (48+i.val)) = labelValue (48+i.val) := by decide +kernel

private theorem step_label_value_b2 : ∀ i : Fin 48, labelValue (nextValue (96+i.val)) = labelValue (96+i.val) := by decide +kernel

private theorem step_label_value_b3 : ∀ i : Fin 48, labelValue (nextValue (144+i.val)) = labelValue (144+i.val) := by decide +kernel

private theorem step_label_value_b4 : ∀ i : Fin 48, labelValue (nextValue (192+i.val)) = labelValue (192+i.val) := by decide +kernel

private theorem step_label_value_b5 : ∀ i : Fin 48, labelValue (nextValue (240+i.val)) = labelValue (240+i.val) := by decide +kernel

private theorem step_label_value_b6 : ∀ i : Fin 48, labelValue (nextValue (288+i.val)) = labelValue (288+i.val) := by decide +kernel

private theorem step_label_value_b7 : ∀ i : Fin 48, labelValue (nextValue (336+i.val)) = labelValue (336+i.val) := by decide +kernel

private theorem step_label_value_b8 : ∀ i : Fin 48, labelValue (nextValue (384+i.val)) = labelValue (384+i.val) := by decide +kernel

private theorem step_label_value_b9 : ∀ i : Fin 48, labelValue (nextValue (432+i.val)) = labelValue (432+i.val) := by decide +kernel

private theorem step_label_value_b10 : ∀ i : Fin 48, labelValue (nextValue (480+i.val)) = labelValue (480+i.val) := by decide +kernel

private theorem step_label_value_b11 : ∀ i : Fin 42, labelValue (nextValue (528+i.val)) = labelValue (528+i.val) := by decide +kernel

private theorem step_label_value_n0_0 : ∀ i : Fin 96, labelValue (nextValue (0+i.val)) = labelValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 0 48 48 step_label_value_b0 step_label_value_b1

private theorem step_label_value_n0_1 : ∀ i : Fin 96, labelValue (nextValue (96+i.val)) = labelValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 96 48 48 step_label_value_b2 step_label_value_b3

private theorem step_label_value_n0_2 : ∀ i : Fin 96, labelValue (nextValue (192+i.val)) = labelValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 192 48 48 step_label_value_b4 step_label_value_b5

private theorem step_label_value_n0_3 : ∀ i : Fin 96, labelValue (nextValue (288+i.val)) = labelValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 288 48 48 step_label_value_b6 step_label_value_b7

private theorem step_label_value_n0_4 : ∀ i : Fin 96, labelValue (nextValue (384+i.val)) = labelValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 384 48 48 step_label_value_b8 step_label_value_b9

private theorem step_label_value_n0_5 : ∀ i : Fin 90, labelValue (nextValue (480+i.val)) = labelValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 480 48 42 step_label_value_b10 step_label_value_b11

private theorem step_label_value_n1_0 : ∀ i : Fin 192, labelValue (nextValue (0+i.val)) = labelValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 0 96 96 step_label_value_n0_0 step_label_value_n0_1

private theorem step_label_value_n1_1 : ∀ i : Fin 192, labelValue (nextValue (192+i.val)) = labelValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 192 96 96 step_label_value_n0_2 step_label_value_n0_3

private theorem step_label_value_n1_2 : ∀ i : Fin 186, labelValue (nextValue (384+i.val)) = labelValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 384 96 90 step_label_value_n0_4 step_label_value_n0_5

private theorem step_label_value_n2_0 : ∀ i : Fin 384, labelValue (nextValue (0+i.val)) = labelValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 0 192 192 step_label_value_n1_0 step_label_value_n1_1

private theorem step_label_value_n3_0 : ∀ i : Fin 570, labelValue (nextValue (0+i.val)) = labelValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (nextValue i) = labelValue i) 0 384 186 step_label_value_n2_0 step_label_value_n1_2

theorem step_label_value : ∀ i : Fin 570, labelValue (nextValue i.val) = labelValue i.val := by
  simpa only [Nat.zero_add] using step_label_value_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
