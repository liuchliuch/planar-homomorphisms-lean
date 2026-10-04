import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertex_zero_root_b0 : ∀ i : Fin 48, vertexRankValue (0+i.val) = 0 → (0+i.val) = vertexRootValue (hostValue (0+i.val)) := by decide +kernel

private theorem vertex_zero_root_b1 : ∀ i : Fin 48, vertexRankValue (48+i.val) = 0 → (48+i.val) = vertexRootValue (hostValue (48+i.val)) := by decide +kernel

private theorem vertex_zero_root_b2 : ∀ i : Fin 48, vertexRankValue (96+i.val) = 0 → (96+i.val) = vertexRootValue (hostValue (96+i.val)) := by decide +kernel

private theorem vertex_zero_root_b3 : ∀ i : Fin 48, vertexRankValue (144+i.val) = 0 → (144+i.val) = vertexRootValue (hostValue (144+i.val)) := by decide +kernel

private theorem vertex_zero_root_b4 : ∀ i : Fin 48, vertexRankValue (192+i.val) = 0 → (192+i.val) = vertexRootValue (hostValue (192+i.val)) := by decide +kernel

private theorem vertex_zero_root_b5 : ∀ i : Fin 48, vertexRankValue (240+i.val) = 0 → (240+i.val) = vertexRootValue (hostValue (240+i.val)) := by decide +kernel

private theorem vertex_zero_root_b6 : ∀ i : Fin 48, vertexRankValue (288+i.val) = 0 → (288+i.val) = vertexRootValue (hostValue (288+i.val)) := by decide +kernel

private theorem vertex_zero_root_b7 : ∀ i : Fin 48, vertexRankValue (336+i.val) = 0 → (336+i.val) = vertexRootValue (hostValue (336+i.val)) := by decide +kernel

private theorem vertex_zero_root_b8 : ∀ i : Fin 48, vertexRankValue (384+i.val) = 0 → (384+i.val) = vertexRootValue (hostValue (384+i.val)) := by decide +kernel

private theorem vertex_zero_root_b9 : ∀ i : Fin 48, vertexRankValue (432+i.val) = 0 → (432+i.val) = vertexRootValue (hostValue (432+i.val)) := by decide +kernel

private theorem vertex_zero_root_b10 : ∀ i : Fin 48, vertexRankValue (480+i.val) = 0 → (480+i.val) = vertexRootValue (hostValue (480+i.val)) := by decide +kernel

private theorem vertex_zero_root_b11 : ∀ i : Fin 42, vertexRankValue (528+i.val) = 0 → (528+i.val) = vertexRootValue (hostValue (528+i.val)) := by decide +kernel

private theorem vertex_zero_root_n0_0 : ∀ i : Fin 96, vertexRankValue (0+i.val) = 0 → (0+i.val) = vertexRootValue (hostValue (0+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 0 48 48 vertex_zero_root_b0 vertex_zero_root_b1

private theorem vertex_zero_root_n0_1 : ∀ i : Fin 96, vertexRankValue (96+i.val) = 0 → (96+i.val) = vertexRootValue (hostValue (96+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 96 48 48 vertex_zero_root_b2 vertex_zero_root_b3

private theorem vertex_zero_root_n0_2 : ∀ i : Fin 96, vertexRankValue (192+i.val) = 0 → (192+i.val) = vertexRootValue (hostValue (192+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 192 48 48 vertex_zero_root_b4 vertex_zero_root_b5

private theorem vertex_zero_root_n0_3 : ∀ i : Fin 96, vertexRankValue (288+i.val) = 0 → (288+i.val) = vertexRootValue (hostValue (288+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 288 48 48 vertex_zero_root_b6 vertex_zero_root_b7

private theorem vertex_zero_root_n0_4 : ∀ i : Fin 96, vertexRankValue (384+i.val) = 0 → (384+i.val) = vertexRootValue (hostValue (384+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 384 48 48 vertex_zero_root_b8 vertex_zero_root_b9

private theorem vertex_zero_root_n0_5 : ∀ i : Fin 90, vertexRankValue (480+i.val) = 0 → (480+i.val) = vertexRootValue (hostValue (480+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 480 48 42 vertex_zero_root_b10 vertex_zero_root_b11

private theorem vertex_zero_root_n1_0 : ∀ i : Fin 192, vertexRankValue (0+i.val) = 0 → (0+i.val) = vertexRootValue (hostValue (0+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 0 96 96 vertex_zero_root_n0_0 vertex_zero_root_n0_1

private theorem vertex_zero_root_n1_1 : ∀ i : Fin 192, vertexRankValue (192+i.val) = 0 → (192+i.val) = vertexRootValue (hostValue (192+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 192 96 96 vertex_zero_root_n0_2 vertex_zero_root_n0_3

private theorem vertex_zero_root_n1_2 : ∀ i : Fin 186, vertexRankValue (384+i.val) = 0 → (384+i.val) = vertexRootValue (hostValue (384+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 384 96 90 vertex_zero_root_n0_4 vertex_zero_root_n0_5

private theorem vertex_zero_root_n2_0 : ∀ i : Fin 384, vertexRankValue (0+i.val) = 0 → (0+i.val) = vertexRootValue (hostValue (0+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 0 192 192 vertex_zero_root_n1_0 vertex_zero_root_n1_1

private theorem vertex_zero_root_n3_0 : ∀ i : Fin 570, vertexRankValue (0+i.val) = 0 → (0+i.val) = vertexRootValue (hostValue (0+i.val)) :=
  FiniteIntervalCheck.append (fun i => vertexRankValue i = 0 → i = vertexRootValue (hostValue i)) 0 384 186 vertex_zero_root_n2_0 vertex_zero_root_n1_2

theorem vertex_zero_root : ∀ i : Fin 570, vertexRankValue i.val = 0 → i.val = vertexRootValue (hostValue i.val) := by
  simpa only [Nat.zero_add] using vertex_zero_root_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
