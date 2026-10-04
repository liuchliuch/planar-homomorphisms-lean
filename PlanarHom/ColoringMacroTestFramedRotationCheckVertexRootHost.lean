import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertex_root_host_b0 : ∀ i : Fin 48, hostValue (vertexRootValue (0+i.val)) = (0+i.val) := by decide +kernel

private theorem vertex_root_host_b1 : ∀ i : Fin 48, hostValue (vertexRootValue (48+i.val)) = (48+i.val) := by decide +kernel

private theorem vertex_root_host_b2 : ∀ i : Fin 22, hostValue (vertexRootValue (96+i.val)) = (96+i.val) := by decide +kernel

private theorem vertex_root_host_n0_0 : ∀ i : Fin 96, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 48 48 vertex_root_host_b0 vertex_root_host_b1

private theorem vertex_root_host_n1_0 : ∀ i : Fin 118, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 96 22 vertex_root_host_n0_0 vertex_root_host_b2

theorem vertex_root_host : ∀ i : Fin 118, hostValue (vertexRootValue i.val) = i.val := by
  simpa only [Nat.zero_add] using vertex_root_host_n1_0

end PlanarHom.ColoringMacroFaces.TestFramed
