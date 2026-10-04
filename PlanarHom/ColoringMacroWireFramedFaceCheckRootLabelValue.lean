import PlanarHom.ColoringMacroWireFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem root_label_value_b0 : ∀ i : Fin 48, labelValue (rootValue (0+i.val)) = (0+i.val) := by decide +kernel

private theorem root_label_value_b1 : ∀ i : Fin 48, labelValue (rootValue (48+i.val)) = (48+i.val) := by decide +kernel

private theorem root_label_value_b2 : ∀ i : Fin 48, labelValue (rootValue (96+i.val)) = (96+i.val) := by decide +kernel

private theorem root_label_value_b3 : ∀ i : Fin 48, labelValue (rootValue (144+i.val)) = (144+i.val) := by decide +kernel

private theorem root_label_value_b4 : ∀ i : Fin 48, labelValue (rootValue (192+i.val)) = (192+i.val) := by decide +kernel

private theorem root_label_value_b5 : ∀ i : Fin 48, labelValue (rootValue (240+i.val)) = (240+i.val) := by decide +kernel

private theorem root_label_value_b6 : ∀ i : Fin 48, labelValue (rootValue (288+i.val)) = (288+i.val) := by decide +kernel

private theorem root_label_value_b7 : ∀ i : Fin 48, labelValue (rootValue (336+i.val)) = (336+i.val) := by decide +kernel

private theorem root_label_value_b8 : ∀ i : Fin 48, labelValue (rootValue (384+i.val)) = (384+i.val) := by decide +kernel

private theorem root_label_value_b9 : ∀ i : Fin 48, labelValue (rootValue (432+i.val)) = (432+i.val) := by decide +kernel

private theorem root_label_value_b10 : ∀ i : Fin 48, labelValue (rootValue (480+i.val)) = (480+i.val) := by decide +kernel

private theorem root_label_value_b11 : ∀ i : Fin 48, labelValue (rootValue (528+i.val)) = (528+i.val) := by decide +kernel

private theorem root_label_value_b12 : ∀ i : Fin 48, labelValue (rootValue (576+i.val)) = (576+i.val) := by decide +kernel

private theorem root_label_value_b13 : ∀ i : Fin 48, labelValue (rootValue (624+i.val)) = (624+i.val) := by decide +kernel

private theorem root_label_value_b14 : ∀ i : Fin 48, labelValue (rootValue (672+i.val)) = (672+i.val) := by decide +kernel

private theorem root_label_value_b15 : ∀ i : Fin 48, labelValue (rootValue (720+i.val)) = (720+i.val) := by decide +kernel

private theorem root_label_value_b16 : ∀ i : Fin 23, labelValue (rootValue (768+i.val)) = (768+i.val) := by decide +kernel

private theorem root_label_value_n0_0 : ∀ i : Fin 96, labelValue (rootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 0 48 48 root_label_value_b0 root_label_value_b1

private theorem root_label_value_n0_1 : ∀ i : Fin 96, labelValue (rootValue (96+i.val)) = (96+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 96 48 48 root_label_value_b2 root_label_value_b3

private theorem root_label_value_n0_2 : ∀ i : Fin 96, labelValue (rootValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 192 48 48 root_label_value_b4 root_label_value_b5

private theorem root_label_value_n0_3 : ∀ i : Fin 96, labelValue (rootValue (288+i.val)) = (288+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 288 48 48 root_label_value_b6 root_label_value_b7

private theorem root_label_value_n0_4 : ∀ i : Fin 96, labelValue (rootValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 384 48 48 root_label_value_b8 root_label_value_b9

private theorem root_label_value_n0_5 : ∀ i : Fin 96, labelValue (rootValue (480+i.val)) = (480+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 480 48 48 root_label_value_b10 root_label_value_b11

private theorem root_label_value_n0_6 : ∀ i : Fin 96, labelValue (rootValue (576+i.val)) = (576+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 576 48 48 root_label_value_b12 root_label_value_b13

private theorem root_label_value_n0_7 : ∀ i : Fin 96, labelValue (rootValue (672+i.val)) = (672+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 672 48 48 root_label_value_b14 root_label_value_b15

private theorem root_label_value_n1_0 : ∀ i : Fin 192, labelValue (rootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 0 96 96 root_label_value_n0_0 root_label_value_n0_1

private theorem root_label_value_n1_1 : ∀ i : Fin 192, labelValue (rootValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 192 96 96 root_label_value_n0_2 root_label_value_n0_3

private theorem root_label_value_n1_2 : ∀ i : Fin 192, labelValue (rootValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 384 96 96 root_label_value_n0_4 root_label_value_n0_5

private theorem root_label_value_n1_3 : ∀ i : Fin 192, labelValue (rootValue (576+i.val)) = (576+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 576 96 96 root_label_value_n0_6 root_label_value_n0_7

private theorem root_label_value_n2_0 : ∀ i : Fin 384, labelValue (rootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 0 192 192 root_label_value_n1_0 root_label_value_n1_1

private theorem root_label_value_n2_1 : ∀ i : Fin 384, labelValue (rootValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 384 192 192 root_label_value_n1_2 root_label_value_n1_3

private theorem root_label_value_n3_0 : ∀ i : Fin 768, labelValue (rootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 0 384 384 root_label_value_n2_0 root_label_value_n2_1

private theorem root_label_value_n4_0 : ∀ i : Fin 791, labelValue (rootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 0 768 23 root_label_value_n3_0 root_label_value_b16

theorem root_label_value : ∀ i : Fin 791, labelValue (rootValue i.val) = i.val := by
  simpa only [Nat.zero_add] using root_label_value_n4_0

end PlanarHom.ColoringMacroFaces.WireFramed
