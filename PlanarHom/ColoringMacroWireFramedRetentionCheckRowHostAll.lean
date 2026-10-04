import PlanarHom.ColoringMacroWireFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_host_all_b0 : ∀ i : Fin 48, (numericRow ⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b1 : ∀ i : Fin 48, (numericRow ⟨(48+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(48+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b2 : ∀ i : Fin 48, (numericRow ⟨(96+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(96+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b3 : ∀ i : Fin 48, (numericRow ⟨(144+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(144+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b4 : ∀ i : Fin 48, (numericRow ⟨(192+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(192+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b5 : ∀ i : Fin 48, (numericRow ⟨(240+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(240+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b6 : ∀ i : Fin 48, (numericRow ⟨(288+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(288+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b7 : ∀ i : Fin 48, (numericRow ⟨(336+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(336+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b8 : ∀ i : Fin 48, (numericRow ⟨(384+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(384+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b9 : ∀ i : Fin 48, (numericRow ⟨(432+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(432+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b10 : ∀ i : Fin 48, (numericRow ⟨(480+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(480+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b11 : ∀ i : Fin 6, (numericRow ⟨(528+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(528+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_n0_0 : ∀ i : Fin 96, (numericRow ⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 0 48 48 row_host_all_b0 row_host_all_b1

private theorem row_host_all_n0_1 : ∀ i : Fin 96, (numericRow ⟨(96+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(96+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 96 48 48 row_host_all_b2 row_host_all_b3

private theorem row_host_all_n0_2 : ∀ i : Fin 96, (numericRow ⟨(192+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(192+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 192 48 48 row_host_all_b4 row_host_all_b5

private theorem row_host_all_n0_3 : ∀ i : Fin 96, (numericRow ⟨(288+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(288+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 288 48 48 row_host_all_b6 row_host_all_b7

private theorem row_host_all_n0_4 : ∀ i : Fin 96, (numericRow ⟨(384+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(384+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 384 48 48 row_host_all_b8 row_host_all_b9

private theorem row_host_all_n0_5 : ∀ i : Fin 54, (numericRow ⟨(480+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(480+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 480 48 6 row_host_all_b10 row_host_all_b11

private theorem row_host_all_n1_0 : ∀ i : Fin 192, (numericRow ⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 0 96 96 row_host_all_n0_0 row_host_all_n0_1

private theorem row_host_all_n1_1 : ∀ i : Fin 192, (numericRow ⟨(192+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(192+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 192 96 96 row_host_all_n0_2 row_host_all_n0_3

private theorem row_host_all_n1_2 : ∀ i : Fin 150, (numericRow ⟨(384+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(384+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 384 96 54 row_host_all_n0_4 row_host_all_n0_5

private theorem row_host_all_n2_0 : ∀ i : Fin 384, (numericRow ⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 0 192 192 row_host_all_n1_0 row_host_all_n1_1

private theorem row_host_all_n3_0 : ∀ i : Fin 534, (numericRow ⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(0+i.val)%534,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%534,Nat.mod_lt _ (by decide)⟩))=true) 0 384 150 row_host_all_n2_0 row_host_all_n1_2

theorem row_host_all : ∀ i : Fin 534, (numericRow ⟨i.val%534,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i.val%534,Nat.mod_lt _ (by decide)⟩))=true := by
  simpa only [Nat.zero_add] using row_host_all_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
