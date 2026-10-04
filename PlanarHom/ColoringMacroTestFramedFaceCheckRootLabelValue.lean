import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem root_label_value_b0 : ∀ i : Fin 48, labelValue (rootValue (0+i.val)) = (0+i.val) := by decide +kernel

private theorem root_label_value_b1 : ∀ i : Fin 48, labelValue (rootValue (48+i.val)) = (48+i.val) := by decide +kernel

private theorem root_label_value_b2 : ∀ i : Fin 48, labelValue (rootValue (96+i.val)) = (96+i.val) := by decide +kernel

private theorem root_label_value_b3 : ∀ i : Fin 25, labelValue (rootValue (144+i.val)) = (144+i.val) := by decide +kernel

private theorem root_label_value_n0_0 : ∀ i : Fin 96, labelValue (rootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 0 48 48 root_label_value_b0 root_label_value_b1

private theorem root_label_value_n0_1 : ∀ i : Fin 73, labelValue (rootValue (96+i.val)) = (96+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 96 48 25 root_label_value_b2 root_label_value_b3

private theorem root_label_value_n1_0 : ∀ i : Fin 169, labelValue (rootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => labelValue (rootValue i) = i) 0 96 73 root_label_value_n0_0 root_label_value_n0_1

theorem root_label_value : ∀ i : Fin 169, labelValue (rootValue i.val) = i.val := by
  simpa only [Nat.zero_add] using root_label_value_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
