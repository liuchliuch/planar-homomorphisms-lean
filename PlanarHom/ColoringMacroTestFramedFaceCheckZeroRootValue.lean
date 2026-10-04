import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem zero_root_value_b0 : ∀ i : Fin 48, rankValue (0+i.val) = 0 → (0+i.val) = rootValue (labelValue (0+i.val)) := by decide +kernel

private theorem zero_root_value_b1 : ∀ i : Fin 48, rankValue (48+i.val) = 0 → (48+i.val) = rootValue (labelValue (48+i.val)) := by decide +kernel

private theorem zero_root_value_b2 : ∀ i : Fin 48, rankValue (96+i.val) = 0 → (96+i.val) = rootValue (labelValue (96+i.val)) := by decide +kernel

private theorem zero_root_value_b3 : ∀ i : Fin 48, rankValue (144+i.val) = 0 → (144+i.val) = rootValue (labelValue (144+i.val)) := by decide +kernel

private theorem zero_root_value_b4 : ∀ i : Fin 48, rankValue (192+i.val) = 0 → (192+i.val) = rootValue (labelValue (192+i.val)) := by decide +kernel

private theorem zero_root_value_b5 : ∀ i : Fin 48, rankValue (240+i.val) = 0 → (240+i.val) = rootValue (labelValue (240+i.val)) := by decide +kernel

private theorem zero_root_value_b6 : ∀ i : Fin 48, rankValue (288+i.val) = 0 → (288+i.val) = rootValue (labelValue (288+i.val)) := by decide +kernel

private theorem zero_root_value_b7 : ∀ i : Fin 48, rankValue (336+i.val) = 0 → (336+i.val) = rootValue (labelValue (336+i.val)) := by decide +kernel

private theorem zero_root_value_b8 : ∀ i : Fin 48, rankValue (384+i.val) = 0 → (384+i.val) = rootValue (labelValue (384+i.val)) := by decide +kernel

private theorem zero_root_value_b9 : ∀ i : Fin 48, rankValue (432+i.val) = 0 → (432+i.val) = rootValue (labelValue (432+i.val)) := by decide +kernel

private theorem zero_root_value_b10 : ∀ i : Fin 48, rankValue (480+i.val) = 0 → (480+i.val) = rootValue (labelValue (480+i.val)) := by decide +kernel

private theorem zero_root_value_b11 : ∀ i : Fin 42, rankValue (528+i.val) = 0 → (528+i.val) = rootValue (labelValue (528+i.val)) := by decide +kernel

private theorem zero_root_value_n0_0 : ∀ i : Fin 96, rankValue (0+i.val) = 0 → (0+i.val) = rootValue (labelValue (0+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 0 48 48 zero_root_value_b0 zero_root_value_b1

private theorem zero_root_value_n0_1 : ∀ i : Fin 96, rankValue (96+i.val) = 0 → (96+i.val) = rootValue (labelValue (96+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 96 48 48 zero_root_value_b2 zero_root_value_b3

private theorem zero_root_value_n0_2 : ∀ i : Fin 96, rankValue (192+i.val) = 0 → (192+i.val) = rootValue (labelValue (192+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 192 48 48 zero_root_value_b4 zero_root_value_b5

private theorem zero_root_value_n0_3 : ∀ i : Fin 96, rankValue (288+i.val) = 0 → (288+i.val) = rootValue (labelValue (288+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 288 48 48 zero_root_value_b6 zero_root_value_b7

private theorem zero_root_value_n0_4 : ∀ i : Fin 96, rankValue (384+i.val) = 0 → (384+i.val) = rootValue (labelValue (384+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 384 48 48 zero_root_value_b8 zero_root_value_b9

private theorem zero_root_value_n0_5 : ∀ i : Fin 90, rankValue (480+i.val) = 0 → (480+i.val) = rootValue (labelValue (480+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 480 48 42 zero_root_value_b10 zero_root_value_b11

private theorem zero_root_value_n1_0 : ∀ i : Fin 192, rankValue (0+i.val) = 0 → (0+i.val) = rootValue (labelValue (0+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 0 96 96 zero_root_value_n0_0 zero_root_value_n0_1

private theorem zero_root_value_n1_1 : ∀ i : Fin 192, rankValue (192+i.val) = 0 → (192+i.val) = rootValue (labelValue (192+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 192 96 96 zero_root_value_n0_2 zero_root_value_n0_3

private theorem zero_root_value_n1_2 : ∀ i : Fin 186, rankValue (384+i.val) = 0 → (384+i.val) = rootValue (labelValue (384+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 384 96 90 zero_root_value_n0_4 zero_root_value_n0_5

private theorem zero_root_value_n2_0 : ∀ i : Fin 384, rankValue (0+i.val) = 0 → (0+i.val) = rootValue (labelValue (0+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 0 192 192 zero_root_value_n1_0 zero_root_value_n1_1

private theorem zero_root_value_n3_0 : ∀ i : Fin 570, rankValue (0+i.val) = 0 → (0+i.val) = rootValue (labelValue (0+i.val)) :=
  FiniteIntervalCheck.append (fun i => rankValue i = 0 → i = rootValue (labelValue i)) 0 384 186 zero_root_value_n2_0 zero_root_value_n1_2

theorem zero_root_value : ∀ i : Fin 570, rankValue i.val = 0 → i.val = rootValue (labelValue i.val) := by
  simpa only [Nat.zero_add] using zero_root_value_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
