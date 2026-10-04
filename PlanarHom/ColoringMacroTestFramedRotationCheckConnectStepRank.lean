import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem connect_step_rank_b0 : ∀ i : Fin 48, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) := by decide +kernel

private theorem connect_step_rank_b1 : ∀ i : Fin 48, 0 < connectRankValue (48+i.val) → connectRankValue (parentValue (48+i.val)) < connectRankValue (48+i.val) := by decide +kernel

private theorem connect_step_rank_b2 : ∀ i : Fin 22, 0 < connectRankValue (96+i.val) → connectRankValue (parentValue (96+i.val)) < connectRankValue (96+i.val) := by decide +kernel

private theorem connect_step_rank_n0_0 : ∀ i : Fin 96, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 48 48 connect_step_rank_b0 connect_step_rank_b1

private theorem connect_step_rank_n1_0 : ∀ i : Fin 118, 0 < connectRankValue (0+i.val) → connectRankValue (parentValue (0+i.val)) < connectRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < connectRankValue i → connectRankValue (parentValue i) < connectRankValue i) 0 96 22 connect_step_rank_n0_0 connect_step_rank_b2

theorem connect_step_rank : ∀ i : Fin 118, 0 < connectRankValue i.val → connectRankValue (parentValue i.val) < connectRankValue i.val := by
  simpa only [Nat.zero_add] using connect_step_rank_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
