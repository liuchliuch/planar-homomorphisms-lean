import PlanarHom.ColoringMacroTestFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_complete_b0 : ∀ i : Fin 48, (⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b1 : ∀ i : Fin 48, (⟨(48+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(48+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b2 : ∀ i : Fin 48, (⟨(96+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(96+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b3 : ∀ i : Fin 48, (⟨(144+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(144+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b4 : ∀ i : Fin 48, (⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b5 : ∀ i : Fin 48, (⟨(240+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(240+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b6 : ∀ i : Fin 48, (⟨(288+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(288+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b7 : ∀ i : Fin 48, (⟨(336+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(336+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b8 : ∀ i : Fin 48, (⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b9 : ∀ i : Fin 48, (⟨(432+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(432+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b10 : ∀ i : Fin 48, (⟨(480+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(480+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_b11 : ∀ i : Fin 42, (⟨(528+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(528+i.val)%570,Nat.mod_lt _ (by decide)⟩) := by decide +kernel

private theorem row_complete_n0_0 : ∀ i : Fin 96, (⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 0 48 48 row_complete_b0 row_complete_b1

private theorem row_complete_n0_1 : ∀ i : Fin 96, (⟨(96+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(96+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 96 48 48 row_complete_b2 row_complete_b3

private theorem row_complete_n0_2 : ∀ i : Fin 96, (⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 192 48 48 row_complete_b4 row_complete_b5

private theorem row_complete_n0_3 : ∀ i : Fin 96, (⟨(288+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(288+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 288 48 48 row_complete_b6 row_complete_b7

private theorem row_complete_n0_4 : ∀ i : Fin 96, (⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 384 48 48 row_complete_b8 row_complete_b9

private theorem row_complete_n0_5 : ∀ i : Fin 90, (⟨(480+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(480+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 480 48 42 row_complete_b10 row_complete_b11

private theorem row_complete_n1_0 : ∀ i : Fin 192, (⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 0 96 96 row_complete_n0_0 row_complete_n0_1

private theorem row_complete_n1_1 : ∀ i : Fin 192, (⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(192+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 192 96 96 row_complete_n0_2 row_complete_n0_3

private theorem row_complete_n1_2 : ∀ i : Fin 186, (⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(384+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 384 96 90 row_complete_n0_4 row_complete_n0_5

private theorem row_complete_n2_0 : ∀ i : Fin 384, (⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 0 192 192 row_complete_n1_0 row_complete_n1_1

private theorem row_complete_n3_0 : ∀ i : Fin 570, (⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨(0+i.val)%570,Nat.mod_lt _ (by decide)⟩) :=
  FiniteIntervalCheck.append (fun i => (⟨i%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i%570,Nat.mod_lt _ (by decide)⟩)) 0 384 186 row_complete_n2_0 row_complete_n1_2

theorem row_complete : ∀ i : Fin 570, (⟨i.val%570,Nat.mod_lt _ (by decide)⟩ : Fin 570)∈numericRow (host ⟨i.val%570,Nat.mod_lt _ (by decide)⟩) := by
  simpa only [Nat.zero_add] using row_complete_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
