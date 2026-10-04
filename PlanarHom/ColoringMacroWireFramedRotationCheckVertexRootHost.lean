import PlanarHom.ColoringMacroWireFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertex_root_host_b0 : ∀ i : Fin 48, hostValue (vertexRootValue (0+i.val)) = (0+i.val) := by decide +kernel

private theorem vertex_root_host_b1 : ∀ i : Fin 48, hostValue (vertexRootValue (48+i.val)) = (48+i.val) := by decide +kernel

private theorem vertex_root_host_b2 : ∀ i : Fin 48, hostValue (vertexRootValue (96+i.val)) = (96+i.val) := by decide +kernel

private theorem vertex_root_host_b3 : ∀ i : Fin 48, hostValue (vertexRootValue (144+i.val)) = (144+i.val) := by decide +kernel

private theorem vertex_root_host_b4 : ∀ i : Fin 48, hostValue (vertexRootValue (192+i.val)) = (192+i.val) := by decide +kernel

private theorem vertex_root_host_b5 : ∀ i : Fin 48, hostValue (vertexRootValue (240+i.val)) = (240+i.val) := by decide +kernel

private theorem vertex_root_host_b6 : ∀ i : Fin 48, hostValue (vertexRootValue (288+i.val)) = (288+i.val) := by decide +kernel

private theorem vertex_root_host_b7 : ∀ i : Fin 48, hostValue (vertexRootValue (336+i.val)) = (336+i.val) := by decide +kernel

private theorem vertex_root_host_b8 : ∀ i : Fin 48, hostValue (vertexRootValue (384+i.val)) = (384+i.val) := by decide +kernel

private theorem vertex_root_host_b9 : ∀ i : Fin 48, hostValue (vertexRootValue (432+i.val)) = (432+i.val) := by decide +kernel

private theorem vertex_root_host_b10 : ∀ i : Fin 48, hostValue (vertexRootValue (480+i.val)) = (480+i.val) := by decide +kernel

private theorem vertex_root_host_b11 : ∀ i : Fin 6, hostValue (vertexRootValue (528+i.val)) = (528+i.val) := by decide +kernel

private theorem vertex_root_host_n0_0 : ∀ i : Fin 96, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 48 48 vertex_root_host_b0 vertex_root_host_b1

private theorem vertex_root_host_n0_1 : ∀ i : Fin 96, hostValue (vertexRootValue (96+i.val)) = (96+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 96 48 48 vertex_root_host_b2 vertex_root_host_b3

private theorem vertex_root_host_n0_2 : ∀ i : Fin 96, hostValue (vertexRootValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 192 48 48 vertex_root_host_b4 vertex_root_host_b5

private theorem vertex_root_host_n0_3 : ∀ i : Fin 96, hostValue (vertexRootValue (288+i.val)) = (288+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 288 48 48 vertex_root_host_b6 vertex_root_host_b7

private theorem vertex_root_host_n0_4 : ∀ i : Fin 96, hostValue (vertexRootValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 384 48 48 vertex_root_host_b8 vertex_root_host_b9

private theorem vertex_root_host_n0_5 : ∀ i : Fin 54, hostValue (vertexRootValue (480+i.val)) = (480+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 480 48 6 vertex_root_host_b10 vertex_root_host_b11

private theorem vertex_root_host_n1_0 : ∀ i : Fin 192, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 96 96 vertex_root_host_n0_0 vertex_root_host_n0_1

private theorem vertex_root_host_n1_1 : ∀ i : Fin 192, hostValue (vertexRootValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 192 96 96 vertex_root_host_n0_2 vertex_root_host_n0_3

private theorem vertex_root_host_n1_2 : ∀ i : Fin 150, hostValue (vertexRootValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 384 96 54 vertex_root_host_n0_4 vertex_root_host_n0_5

private theorem vertex_root_host_n2_0 : ∀ i : Fin 384, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 192 192 vertex_root_host_n1_0 vertex_root_host_n1_1

private theorem vertex_root_host_n3_0 : ∀ i : Fin 534, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 384 150 vertex_root_host_n2_0 vertex_root_host_n1_2

theorem vertex_root_host : ∀ i : Fin 534, hostValue (vertexRootValue i.val) = i.val := by
  simpa only [Nat.zero_add] using vertex_root_host_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
