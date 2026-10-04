import PlanarHom.ColoringMacroWireFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem connect_adjacent_b0 : ∀ i : Fin 48, 0 < connectRankValue (0+i.val) → ((hostValue (2*parentEdgeValue (0+i.val)) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)+1) = parentValue (0+i.val)) ∨ (hostValue (2*parentEdgeValue (0+i.val)+1) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)) = parentValue (0+i.val))) := by decide +kernel

private theorem connect_adjacent_b1 : ∀ i : Fin 48, 0 < connectRankValue (48+i.val) → ((hostValue (2*parentEdgeValue (48+i.val)) = (48+i.val) ∧ hostValue (2*parentEdgeValue (48+i.val)+1) = parentValue (48+i.val)) ∨ (hostValue (2*parentEdgeValue (48+i.val)+1) = (48+i.val) ∧ hostValue (2*parentEdgeValue (48+i.val)) = parentValue (48+i.val))) := by decide +kernel

private theorem connect_adjacent_b2 : ∀ i : Fin 48, 0 < connectRankValue (96+i.val) → ((hostValue (2*parentEdgeValue (96+i.val)) = (96+i.val) ∧ hostValue (2*parentEdgeValue (96+i.val)+1) = parentValue (96+i.val)) ∨ (hostValue (2*parentEdgeValue (96+i.val)+1) = (96+i.val) ∧ hostValue (2*parentEdgeValue (96+i.val)) = parentValue (96+i.val))) := by decide +kernel

private theorem connect_adjacent_b3 : ∀ i : Fin 48, 0 < connectRankValue (144+i.val) → ((hostValue (2*parentEdgeValue (144+i.val)) = (144+i.val) ∧ hostValue (2*parentEdgeValue (144+i.val)+1) = parentValue (144+i.val)) ∨ (hostValue (2*parentEdgeValue (144+i.val)+1) = (144+i.val) ∧ hostValue (2*parentEdgeValue (144+i.val)) = parentValue (144+i.val))) := by decide +kernel

private theorem connect_adjacent_b4 : ∀ i : Fin 48, 0 < connectRankValue (192+i.val) → ((hostValue (2*parentEdgeValue (192+i.val)) = (192+i.val) ∧ hostValue (2*parentEdgeValue (192+i.val)+1) = parentValue (192+i.val)) ∨ (hostValue (2*parentEdgeValue (192+i.val)+1) = (192+i.val) ∧ hostValue (2*parentEdgeValue (192+i.val)) = parentValue (192+i.val))) := by decide +kernel

private theorem connect_adjacent_b5 : ∀ i : Fin 48, 0 < connectRankValue (240+i.val) → ((hostValue (2*parentEdgeValue (240+i.val)) = (240+i.val) ∧ hostValue (2*parentEdgeValue (240+i.val)+1) = parentValue (240+i.val)) ∨ (hostValue (2*parentEdgeValue (240+i.val)+1) = (240+i.val) ∧ hostValue (2*parentEdgeValue (240+i.val)) = parentValue (240+i.val))) := by decide +kernel

private theorem connect_adjacent_b6 : ∀ i : Fin 48, 0 < connectRankValue (288+i.val) → ((hostValue (2*parentEdgeValue (288+i.val)) = (288+i.val) ∧ hostValue (2*parentEdgeValue (288+i.val)+1) = parentValue (288+i.val)) ∨ (hostValue (2*parentEdgeValue (288+i.val)+1) = (288+i.val) ∧ hostValue (2*parentEdgeValue (288+i.val)) = parentValue (288+i.val))) := by decide +kernel

private theorem connect_adjacent_b7 : ∀ i : Fin 48, 0 < connectRankValue (336+i.val) → ((hostValue (2*parentEdgeValue (336+i.val)) = (336+i.val) ∧ hostValue (2*parentEdgeValue (336+i.val)+1) = parentValue (336+i.val)) ∨ (hostValue (2*parentEdgeValue (336+i.val)+1) = (336+i.val) ∧ hostValue (2*parentEdgeValue (336+i.val)) = parentValue (336+i.val))) := by decide +kernel

private theorem connect_adjacent_b8 : ∀ i : Fin 48, 0 < connectRankValue (384+i.val) → ((hostValue (2*parentEdgeValue (384+i.val)) = (384+i.val) ∧ hostValue (2*parentEdgeValue (384+i.val)+1) = parentValue (384+i.val)) ∨ (hostValue (2*parentEdgeValue (384+i.val)+1) = (384+i.val) ∧ hostValue (2*parentEdgeValue (384+i.val)) = parentValue (384+i.val))) := by decide +kernel

private theorem connect_adjacent_b9 : ∀ i : Fin 48, 0 < connectRankValue (432+i.val) → ((hostValue (2*parentEdgeValue (432+i.val)) = (432+i.val) ∧ hostValue (2*parentEdgeValue (432+i.val)+1) = parentValue (432+i.val)) ∨ (hostValue (2*parentEdgeValue (432+i.val)+1) = (432+i.val) ∧ hostValue (2*parentEdgeValue (432+i.val)) = parentValue (432+i.val))) := by decide +kernel

private theorem connect_adjacent_b10 : ∀ i : Fin 48, 0 < connectRankValue (480+i.val) → ((hostValue (2*parentEdgeValue (480+i.val)) = (480+i.val) ∧ hostValue (2*parentEdgeValue (480+i.val)+1) = parentValue (480+i.val)) ∨ (hostValue (2*parentEdgeValue (480+i.val)+1) = (480+i.val) ∧ hostValue (2*parentEdgeValue (480+i.val)) = parentValue (480+i.val))) := by decide +kernel

private theorem connect_adjacent_b11 : ∀ i : Fin 6, 0 < connectRankValue (528+i.val) → ((hostValue (2*parentEdgeValue (528+i.val)) = (528+i.val) ∧ hostValue (2*parentEdgeValue (528+i.val)+1) = parentValue (528+i.val)) ∨ (hostValue (2*parentEdgeValue (528+i.val)+1) = (528+i.val) ∧ hostValue (2*parentEdgeValue (528+i.val)) = parentValue (528+i.val))) := by decide +kernel

private theorem connect_adjacent_n0_0 : ∀ i : Fin 96, 0 < connectRankValue (0+i.val) → ((hostValue (2*parentEdgeValue (0+i.val)) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)+1) = parentValue (0+i.val)) ∨ (hostValue (2*parentEdgeValue (0+i.val)+1) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)) = parentValue (0+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 0 48 48 connect_adjacent_b0 connect_adjacent_b1

private theorem connect_adjacent_n0_1 : ∀ i : Fin 96, 0 < connectRankValue (96+i.val) → ((hostValue (2*parentEdgeValue (96+i.val)) = (96+i.val) ∧ hostValue (2*parentEdgeValue (96+i.val)+1) = parentValue (96+i.val)) ∨ (hostValue (2*parentEdgeValue (96+i.val)+1) = (96+i.val) ∧ hostValue (2*parentEdgeValue (96+i.val)) = parentValue (96+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 96 48 48 connect_adjacent_b2 connect_adjacent_b3

private theorem connect_adjacent_n0_2 : ∀ i : Fin 96, 0 < connectRankValue (192+i.val) → ((hostValue (2*parentEdgeValue (192+i.val)) = (192+i.val) ∧ hostValue (2*parentEdgeValue (192+i.val)+1) = parentValue (192+i.val)) ∨ (hostValue (2*parentEdgeValue (192+i.val)+1) = (192+i.val) ∧ hostValue (2*parentEdgeValue (192+i.val)) = parentValue (192+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 192 48 48 connect_adjacent_b4 connect_adjacent_b5

private theorem connect_adjacent_n0_3 : ∀ i : Fin 96, 0 < connectRankValue (288+i.val) → ((hostValue (2*parentEdgeValue (288+i.val)) = (288+i.val) ∧ hostValue (2*parentEdgeValue (288+i.val)+1) = parentValue (288+i.val)) ∨ (hostValue (2*parentEdgeValue (288+i.val)+1) = (288+i.val) ∧ hostValue (2*parentEdgeValue (288+i.val)) = parentValue (288+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 288 48 48 connect_adjacent_b6 connect_adjacent_b7

private theorem connect_adjacent_n0_4 : ∀ i : Fin 96, 0 < connectRankValue (384+i.val) → ((hostValue (2*parentEdgeValue (384+i.val)) = (384+i.val) ∧ hostValue (2*parentEdgeValue (384+i.val)+1) = parentValue (384+i.val)) ∨ (hostValue (2*parentEdgeValue (384+i.val)+1) = (384+i.val) ∧ hostValue (2*parentEdgeValue (384+i.val)) = parentValue (384+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 384 48 48 connect_adjacent_b8 connect_adjacent_b9

private theorem connect_adjacent_n0_5 : ∀ i : Fin 54, 0 < connectRankValue (480+i.val) → ((hostValue (2*parentEdgeValue (480+i.val)) = (480+i.val) ∧ hostValue (2*parentEdgeValue (480+i.val)+1) = parentValue (480+i.val)) ∨ (hostValue (2*parentEdgeValue (480+i.val)+1) = (480+i.val) ∧ hostValue (2*parentEdgeValue (480+i.val)) = parentValue (480+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 480 48 6 connect_adjacent_b10 connect_adjacent_b11

private theorem connect_adjacent_n1_0 : ∀ i : Fin 192, 0 < connectRankValue (0+i.val) → ((hostValue (2*parentEdgeValue (0+i.val)) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)+1) = parentValue (0+i.val)) ∨ (hostValue (2*parentEdgeValue (0+i.val)+1) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)) = parentValue (0+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 0 96 96 connect_adjacent_n0_0 connect_adjacent_n0_1

private theorem connect_adjacent_n1_1 : ∀ i : Fin 192, 0 < connectRankValue (192+i.val) → ((hostValue (2*parentEdgeValue (192+i.val)) = (192+i.val) ∧ hostValue (2*parentEdgeValue (192+i.val)+1) = parentValue (192+i.val)) ∨ (hostValue (2*parentEdgeValue (192+i.val)+1) = (192+i.val) ∧ hostValue (2*parentEdgeValue (192+i.val)) = parentValue (192+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 192 96 96 connect_adjacent_n0_2 connect_adjacent_n0_3

private theorem connect_adjacent_n1_2 : ∀ i : Fin 150, 0 < connectRankValue (384+i.val) → ((hostValue (2*parentEdgeValue (384+i.val)) = (384+i.val) ∧ hostValue (2*parentEdgeValue (384+i.val)+1) = parentValue (384+i.val)) ∨ (hostValue (2*parentEdgeValue (384+i.val)+1) = (384+i.val) ∧ hostValue (2*parentEdgeValue (384+i.val)) = parentValue (384+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 384 96 54 connect_adjacent_n0_4 connect_adjacent_n0_5

private theorem connect_adjacent_n2_0 : ∀ i : Fin 384, 0 < connectRankValue (0+i.val) → ((hostValue (2*parentEdgeValue (0+i.val)) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)+1) = parentValue (0+i.val)) ∨ (hostValue (2*parentEdgeValue (0+i.val)+1) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)) = parentValue (0+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 0 192 192 connect_adjacent_n1_0 connect_adjacent_n1_1

private theorem connect_adjacent_n3_0 : ∀ i : Fin 534, 0 < connectRankValue (0+i.val) → ((hostValue (2*parentEdgeValue (0+i.val)) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)+1) = parentValue (0+i.val)) ∨ (hostValue (2*parentEdgeValue (0+i.val)+1) = (0+i.val) ∧ hostValue (2*parentEdgeValue (0+i.val)) = parentValue (0+i.val))) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → ((hostValue (2*parentEdgeValue i) = i ∧ hostValue (2*parentEdgeValue i+1) = parentValue i) ∨ (hostValue (2*parentEdgeValue i+1) = i ∧ hostValue (2*parentEdgeValue i) = parentValue i))) 0 384 150 connect_adjacent_n2_0 connect_adjacent_n1_2

theorem connect_adjacent : ∀ i : Fin 534, 0 < connectRankValue i.val → ((hostValue (2*parentEdgeValue i.val) = i.val ∧ hostValue (2*parentEdgeValue i.val+1) = parentValue i.val) ∨ (hostValue (2*parentEdgeValue i.val+1) = i.val ∧ hostValue (2*parentEdgeValue i.val) = parentValue i.val)) := by
  simpa only [Nat.zero_add] using connect_adjacent_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
