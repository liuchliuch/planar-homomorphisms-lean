import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem connect_zero_root_b0 : ∀ i : Fin 48, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b1 : ∀ i : Fin 48, connectRankValue (48+i.val) = 0 → (48+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_b2 : ∀ i : Fin 22, connectRankValue (96+i.val) = 0 → (96+i.val) = 0 := by decide +kernel

private theorem connect_zero_root_n0_0 : ∀ i : Fin 96, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 48 48 connect_zero_root_b0 connect_zero_root_b1

private theorem connect_zero_root_n1_0 : ∀ i : Fin 118, connectRankValue (0+i.val) = 0 → (0+i.val) = 0 :=
  FiniteIntervalCheck.append (fun i => connectRankValue i = 0 → i = 0) 0 96 22 connect_zero_root_n0_0 connect_zero_root_b2

theorem connect_zero_root : ∀ i : Fin 118, connectRankValue i.val = 0 → i.val = 0 := by
  simpa only [Nat.zero_add] using connect_zero_root_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
