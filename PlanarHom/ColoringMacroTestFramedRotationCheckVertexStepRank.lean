import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertex_step_rank_b0 : ∀ i : Fin 48, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) := by decide +kernel

private theorem vertex_step_rank_b1 : ∀ i : Fin 48, 0 < vertexRankValue (48+i.val) → vertexRankValue (rotateValue (48+i.val)) + 1 = vertexRankValue (48+i.val) := by decide +kernel

private theorem vertex_step_rank_b2 : ∀ i : Fin 48, 0 < vertexRankValue (96+i.val) → vertexRankValue (rotateValue (96+i.val)) + 1 = vertexRankValue (96+i.val) := by decide +kernel

private theorem vertex_step_rank_b3 : ∀ i : Fin 48, 0 < vertexRankValue (144+i.val) → vertexRankValue (rotateValue (144+i.val)) + 1 = vertexRankValue (144+i.val) := by decide +kernel

private theorem vertex_step_rank_b4 : ∀ i : Fin 48, 0 < vertexRankValue (192+i.val) → vertexRankValue (rotateValue (192+i.val)) + 1 = vertexRankValue (192+i.val) := by decide +kernel

private theorem vertex_step_rank_b5 : ∀ i : Fin 48, 0 < vertexRankValue (240+i.val) → vertexRankValue (rotateValue (240+i.val)) + 1 = vertexRankValue (240+i.val) := by decide +kernel

private theorem vertex_step_rank_b6 : ∀ i : Fin 48, 0 < vertexRankValue (288+i.val) → vertexRankValue (rotateValue (288+i.val)) + 1 = vertexRankValue (288+i.val) := by decide +kernel

private theorem vertex_step_rank_b7 : ∀ i : Fin 48, 0 < vertexRankValue (336+i.val) → vertexRankValue (rotateValue (336+i.val)) + 1 = vertexRankValue (336+i.val) := by decide +kernel

private theorem vertex_step_rank_b8 : ∀ i : Fin 48, 0 < vertexRankValue (384+i.val) → vertexRankValue (rotateValue (384+i.val)) + 1 = vertexRankValue (384+i.val) := by decide +kernel

private theorem vertex_step_rank_b9 : ∀ i : Fin 48, 0 < vertexRankValue (432+i.val) → vertexRankValue (rotateValue (432+i.val)) + 1 = vertexRankValue (432+i.val) := by decide +kernel

private theorem vertex_step_rank_b10 : ∀ i : Fin 48, 0 < vertexRankValue (480+i.val) → vertexRankValue (rotateValue (480+i.val)) + 1 = vertexRankValue (480+i.val) := by decide +kernel

private theorem vertex_step_rank_b11 : ∀ i : Fin 42, 0 < vertexRankValue (528+i.val) → vertexRankValue (rotateValue (528+i.val)) + 1 = vertexRankValue (528+i.val) := by decide +kernel

private theorem vertex_step_rank_n0_0 : ∀ i : Fin 96, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 48 48 vertex_step_rank_b0 vertex_step_rank_b1

private theorem vertex_step_rank_n0_1 : ∀ i : Fin 96, 0 < vertexRankValue (96+i.val) → vertexRankValue (rotateValue (96+i.val)) + 1 = vertexRankValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 96 48 48 vertex_step_rank_b2 vertex_step_rank_b3

private theorem vertex_step_rank_n0_2 : ∀ i : Fin 96, 0 < vertexRankValue (192+i.val) → vertexRankValue (rotateValue (192+i.val)) + 1 = vertexRankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 192 48 48 vertex_step_rank_b4 vertex_step_rank_b5

private theorem vertex_step_rank_n0_3 : ∀ i : Fin 96, 0 < vertexRankValue (288+i.val) → vertexRankValue (rotateValue (288+i.val)) + 1 = vertexRankValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 288 48 48 vertex_step_rank_b6 vertex_step_rank_b7

private theorem vertex_step_rank_n0_4 : ∀ i : Fin 96, 0 < vertexRankValue (384+i.val) → vertexRankValue (rotateValue (384+i.val)) + 1 = vertexRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 384 48 48 vertex_step_rank_b8 vertex_step_rank_b9

private theorem vertex_step_rank_n0_5 : ∀ i : Fin 90, 0 < vertexRankValue (480+i.val) → vertexRankValue (rotateValue (480+i.val)) + 1 = vertexRankValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 480 48 42 vertex_step_rank_b10 vertex_step_rank_b11

private theorem vertex_step_rank_n1_0 : ∀ i : Fin 192, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 96 96 vertex_step_rank_n0_0 vertex_step_rank_n0_1

private theorem vertex_step_rank_n1_1 : ∀ i : Fin 192, 0 < vertexRankValue (192+i.val) → vertexRankValue (rotateValue (192+i.val)) + 1 = vertexRankValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 192 96 96 vertex_step_rank_n0_2 vertex_step_rank_n0_3

private theorem vertex_step_rank_n1_2 : ∀ i : Fin 186, 0 < vertexRankValue (384+i.val) → vertexRankValue (rotateValue (384+i.val)) + 1 = vertexRankValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 384 96 90 vertex_step_rank_n0_4 vertex_step_rank_n0_5

private theorem vertex_step_rank_n2_0 : ∀ i : Fin 384, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 192 192 vertex_step_rank_n1_0 vertex_step_rank_n1_1

private theorem vertex_step_rank_n3_0 : ∀ i : Fin 570, 0 < vertexRankValue (0+i.val) → vertexRankValue (rotateValue (0+i.val)) + 1 = vertexRankValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => 0 < vertexRankValue i → vertexRankValue (rotateValue i) + 1 = vertexRankValue i) 0 384 186 vertex_step_rank_n2_0 vertex_step_rank_n1_2

theorem vertex_step_rank : ∀ i : Fin 570, 0 < vertexRankValue i.val → vertexRankValue (rotateValue i.val) + 1 = vertexRankValue i.val := by
  simpa only [Nat.zero_add] using vertex_step_rank_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
