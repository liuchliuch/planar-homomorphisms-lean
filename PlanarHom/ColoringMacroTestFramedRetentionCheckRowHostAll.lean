import PlanarHom.ColoringMacroTestFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_host_all_b0 : ∀ i : Fin 48, (numericRow ⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b1 : ∀ i : Fin 48, (numericRow ⟨(48+i.val)%118,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(48+i.val)%118,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_b2 : ∀ i : Fin 22, (numericRow ⟨(96+i.val)%118,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(96+i.val)%118,Nat.mod_lt _ (by decide)⟩))=true := by decide +kernel

private theorem row_host_all_n0_0 : ∀ i : Fin 96, (numericRow ⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%118,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%118,Nat.mod_lt _ (by decide)⟩))=true) 0 48 48 row_host_all_b0 row_host_all_b1

private theorem row_host_all_n1_0 : ∀ i : Fin 118, (numericRow ⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩))=true :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%118,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i%118,Nat.mod_lt _ (by decide)⟩))=true) 0 96 22 row_host_all_n0_0 row_host_all_b2

theorem row_host_all : ∀ i : Fin 118, (numericRow ⟨i.val%118,Nat.mod_lt _ (by decide)⟩).all (fun d => decide (host d=⟨i.val%118,Nat.mod_lt _ (by decide)⟩))=true := by
  simpa only [Nat.zero_add] using row_host_all_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
