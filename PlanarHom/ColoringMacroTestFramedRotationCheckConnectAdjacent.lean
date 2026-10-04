import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem connect_adjacent_b0 : ∀ i : Fin 48, 0 < connectRankValue (0+i.val) → ((hostValue (2*parentEdgeValue (0+i.val)) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)+1) = parentValue (0+i.val)) ∨ (hostValue (2*parentEdgeValue (0+i.val)+1) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)) = parentValue (0+i.val))) := by decide +kernel

private theorem connect_adjacent_b1 : ∀ i : Fin 48, 0 < connectRankValue (48+i.val) → ((hostValue (2*parentEdgeValue (48+i.val)) = (48+i.val) ∧ hostValue (2*parentEdgeValue (48+i.val)+1) = parentValue (48+i.val)) ∨ (hostValue (2*parentEdgeValue (48+i.val)+1) = (48+i.val) ∧ hostValue (2*parentEdgeValue (48+i.val)) = parentValue (48+i.val))) := by decide +kernel

private theorem connect_adjacent_b2 : ∀ i : Fin 22, 0 < connectRankValue (96+i.val) → ((hostValue (2*parentEdgeValue (96+i.val)) = (96+i.val) ∧ hostValue (2*parentEdgeValue (96+i.val)+1) = parentValue (96+i.val)) ∨ (hostValue (2*parentEdgeValue (96+i.val)+1) = (96+i.val) ∧ hostValue (2*parentEdgeValue (96+i.val)) = parentValue (96+i.val))) := by decide +kernel

private theorem connect_adjacent_n0_0 : ∀ i : Fin 96, 0 < connectRankValue (0+i.val) → ((hostValue (2*parentEdgeValue (0+i.val)) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)+1) = parentValue (0+i.val)) ∨ (hostValue (2*parentEdgeValue (0+i.val)+1) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)) = parentValue (0+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 0 48 48 connect_adjacent_b0 connect_adjacent_b1

private theorem connect_adjacent_n1_0 : ∀ i : Fin 118, 0 < connectRankValue (0+i.val) → ((hostValue (2*parentEdgeValue (0+i.val)) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)+1) = parentValue (0+i.val)) ∨ (hostValue (2*parentEdgeValue (0+i.val)+1) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)) = parentValue (0+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 0 96 22 connect_adjacent_n0_0 connect_adjacent_b2

theorem connect_adjacent : ∀ i : Fin 118, 0 < connectRankValue i.val → ((hostValue (2*parentEdgeValue i.val) = i.val ∧ hostValue (2*parentEdgeValue i.val+1) = parentValue i.val) ∨ (hostValue (2*parentEdgeValue i.val+1) = i.val ∧ hostValue (2*parentEdgeValue i.val) = parentValue i.val)) := by
  simpa only [Nat.zero_add] using connect_adjacent_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
