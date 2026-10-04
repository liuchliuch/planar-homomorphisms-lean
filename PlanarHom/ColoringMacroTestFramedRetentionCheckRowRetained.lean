import PlanarHom.ColoringMacroTestFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_retained_b0 : ∀ i : Fin 48, retainedRawRow ⟨(0+i.val)%114,Nat.mod_lt _ (by decide)⟩=ColoringTestMacroRows.raw ⟨(0+i.val)%114,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b1 : ∀ i : Fin 48, retainedRawRow ⟨(48+i.val)%114,Nat.mod_lt _ (by decide)⟩=ColoringTestMacroRows.raw ⟨(48+i.val)%114,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b2 : ∀ i : Fin 18, retainedRawRow ⟨(96+i.val)%114,Nat.mod_lt _ (by decide)⟩=ColoringTestMacroRows.raw ⟨(96+i.val)%114,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_n0_0 : ∀ i : Fin 96, retainedRawRow ⟨(0+i.val)%114,Nat.mod_lt _ (by decide)⟩=ColoringTestMacroRows.raw ⟨(0+i.val)%114,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%114,Nat.mod_lt _ (by decide)⟩=ColoringTestMacroRows.raw ⟨i%114,Nat.mod_lt _ (by decide)⟩) 0 48 48 row_retained_b0 row_retained_b1

private theorem row_retained_n1_0 : ∀ i : Fin 114, retainedRawRow ⟨(0+i.val)%114,Nat.mod_lt _ (by decide)⟩=ColoringTestMacroRows.raw ⟨(0+i.val)%114,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%114,Nat.mod_lt _ (by decide)⟩=ColoringTestMacroRows.raw ⟨i%114,Nat.mod_lt _ (by decide)⟩) 0 96 18 row_retained_n0_0 row_retained_b2

theorem row_retained : ∀ i : Fin 114, retainedRawRow ⟨i.val%114,Nat.mod_lt _ (by decide)⟩=ColoringTestMacroRows.raw ⟨i.val%114,Nat.mod_lt _ (by decide)⟩ := by
  simpa only [Nat.zero_add] using row_retained_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
