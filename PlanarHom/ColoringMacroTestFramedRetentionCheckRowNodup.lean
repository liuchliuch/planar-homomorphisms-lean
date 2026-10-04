import PlanarHom.ColoringMacroTestFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_nodup_b0 : ∀ i : Fin 48, (numericRow ⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b1 : ∀ i : Fin 48, (numericRow ⟨(48+i.val)%118,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b2 : ∀ i : Fin 22, (numericRow ⟨(96+i.val)%118,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_n0_0 : ∀ i : Fin 96, (numericRow ⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%118,Nat.mod_lt _ (by decide)⟩).Nodup) 0 48 48 row_nodup_b0 row_nodup_b1

private theorem row_nodup_n1_0 : ∀ i : Fin 118, (numericRow ⟨(0+i.val)%118,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%118,Nat.mod_lt _ (by decide)⟩).Nodup) 0 96 22 row_nodup_n0_0 row_nodup_b2

theorem row_nodup : ∀ i : Fin 118, (numericRow ⟨i.val%118,Nat.mod_lt _ (by decide)⟩).Nodup := by
  simpa only [Nat.zero_add] using row_nodup_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
