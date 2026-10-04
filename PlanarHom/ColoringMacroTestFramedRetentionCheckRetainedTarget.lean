import PlanarHom.ColoringMacroTestFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem retained_target_b0 : ∀ i : Fin 48, hostValue (2*(0+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(0+i.val)%272,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem retained_target_b1 : ∀ i : Fin 48, hostValue (2*(48+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(48+i.val)%272,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem retained_target_b2 : ∀ i : Fin 48, hostValue (2*(96+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(96+i.val)%272,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem retained_target_b3 : ∀ i : Fin 48, hostValue (2*(144+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(144+i.val)%272,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem retained_target_b4 : ∀ i : Fin 48, hostValue (2*(192+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(192+i.val)%272,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem retained_target_b5 : ∀ i : Fin 32, hostValue (2*(240+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(240+i.val)%272,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem retained_target_n0_0 : ∀ i : Fin 96, hostValue (2*(0+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(0+i.val)%272,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => hostValue (2*i+1) = ColoringTestMacroCoordinates.targetNat ⟨i%272,Nat.mod_lt _ (by decide)⟩) 0 48 48 retained_target_b0 retained_target_b1

private theorem retained_target_n0_1 : ∀ i : Fin 96, hostValue (2*(96+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(96+i.val)%272,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => hostValue (2*i+1) = ColoringTestMacroCoordinates.targetNat ⟨i%272,Nat.mod_lt _ (by decide)⟩) 96 48 48 retained_target_b2 retained_target_b3

private theorem retained_target_n0_2 : ∀ i : Fin 80, hostValue (2*(192+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(192+i.val)%272,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => hostValue (2*i+1) = ColoringTestMacroCoordinates.targetNat ⟨i%272,Nat.mod_lt _ (by decide)⟩) 192 48 32 retained_target_b4 retained_target_b5

private theorem retained_target_n1_0 : ∀ i : Fin 192, hostValue (2*(0+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(0+i.val)%272,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => hostValue (2*i+1) = ColoringTestMacroCoordinates.targetNat ⟨i%272,Nat.mod_lt _ (by decide)⟩) 0 96 96 retained_target_n0_0 retained_target_n0_1

private theorem retained_target_n2_0 : ∀ i : Fin 272, hostValue (2*(0+i.val)+1) = ColoringTestMacroCoordinates.targetNat ⟨(0+i.val)%272,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => hostValue (2*i+1) = ColoringTestMacroCoordinates.targetNat ⟨i%272,Nat.mod_lt _ (by decide)⟩) 0 192 80 retained_target_n1_0 retained_target_n0_2

theorem retained_target : ∀ i : Fin 272, hostValue (2*i.val+1) = ColoringTestMacroCoordinates.targetNat ⟨i.val%272,Nat.mod_lt _ (by decide)⟩ := by
  simpa only [Nat.zero_add] using retained_target_n2_0

end PlanarHom.ColoringMacroFaces.TestFramed
