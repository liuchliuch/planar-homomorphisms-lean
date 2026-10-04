import PlanarHom.ColoringMacroTestFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_rotation_b0 : ∀ i : Fin 48, ((numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) := by decide +kernel

private theorem row_rotation_b1 : ∀ i : Fin 48, ((numericRow (host ⟨(48+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(48+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (48+i.val) := by decide +kernel

private theorem row_rotation_b2 : ∀ i : Fin 48, ((numericRow (host ⟨(96+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(96+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (96+i.val) := by decide +kernel

private theorem row_rotation_b3 : ∀ i : Fin 48, ((numericRow (host ⟨(144+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(144+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (144+i.val) := by decide +kernel

private theorem row_rotation_b4 : ∀ i : Fin 48, ((numericRow (host ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (192+i.val) := by decide +kernel

private theorem row_rotation_b5 : ∀ i : Fin 48, ((numericRow (host ⟨(240+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(240+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (240+i.val) := by decide +kernel

private theorem row_rotation_b6 : ∀ i : Fin 48, ((numericRow (host ⟨(288+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(288+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (288+i.val) := by decide +kernel

private theorem row_rotation_b7 : ∀ i : Fin 48, ((numericRow (host ⟨(336+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(336+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (336+i.val) := by decide +kernel

private theorem row_rotation_b8 : ∀ i : Fin 48, ((numericRow (host ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (384+i.val) := by decide +kernel

private theorem row_rotation_b9 : ∀ i : Fin 48, ((numericRow (host ⟨(432+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(432+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (432+i.val) := by decide +kernel

private theorem row_rotation_b10 : ∀ i : Fin 48, ((numericRow (host ⟨(480+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(480+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (480+i.val) := by decide +kernel

private theorem row_rotation_b11 : ∀ i : Fin 42, ((numericRow (host ⟨(528+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(528+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (528+i.val) := by decide +kernel

private theorem row_rotation_n0_0 : ∀ i : Fin 96, ((numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 48 48 row_rotation_b0 row_rotation_b1

private theorem row_rotation_n0_1 : ∀ i : Fin 96, ((numericRow (host ⟨(96+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(96+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 96 48 48 row_rotation_b2 row_rotation_b3

private theorem row_rotation_n0_2 : ∀ i : Fin 96, ((numericRow (host ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 192 48 48 row_rotation_b4 row_rotation_b5

private theorem row_rotation_n0_3 : ∀ i : Fin 96, ((numericRow (host ⟨(288+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(288+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 288 48 48 row_rotation_b6 row_rotation_b7

private theorem row_rotation_n0_4 : ∀ i : Fin 96, ((numericRow (host ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 384 48 48 row_rotation_b8 row_rotation_b9

private theorem row_rotation_n0_5 : ∀ i : Fin 90, ((numericRow (host ⟨(480+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(480+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 480 48 42 row_rotation_b10 row_rotation_b11

private theorem row_rotation_n1_0 : ∀ i : Fin 192, ((numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 96 96 row_rotation_n0_0 row_rotation_n0_1

private theorem row_rotation_n1_1 : ∀ i : Fin 192, ((numericRow (host ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 192 96 96 row_rotation_n0_2 row_rotation_n0_3

private theorem row_rotation_n1_2 : ∀ i : Fin 186, ((numericRow (host ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 384 96 90 row_rotation_n0_4 row_rotation_n0_5

private theorem row_rotation_n2_0 : ∀ i : Fin 384, ((numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 192 192 row_rotation_n1_0 row_rotation_n1_1

private theorem row_rotation_n3_0 : ∀ i : Fin 570, ((numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => ((numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i) 0 384 186 row_rotation_n2_0 row_rotation_n1_2

theorem row_rotation : ∀ i : Fin 570, ((numericRow (host ⟨i.val%570,Nat.mod_lt _ (by decide)⟩)).formPerm ⟨i.val%570,Nat.mod_lt _ (by decide)⟩).val=rotateValue i.val := by
  simpa only [Nat.zero_add] using row_rotation_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
