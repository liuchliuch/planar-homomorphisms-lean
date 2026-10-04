import PlanarHom.ColoringMacroTestFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem vertex_step_host_b0 : ∀ i : Fin 48, hostValue (rotateValue (0+i.val)) = hostValue (0+i.val) := by decide +kernel

private theorem vertex_step_host_b1 : ∀ i : Fin 48, hostValue (rotateValue (48+i.val)) = hostValue (48+i.val) := by decide +kernel

private theorem vertex_step_host_b2 : ∀ i : Fin 48, hostValue (rotateValue (96+i.val)) = hostValue (96+i.val) := by decide +kernel

private theorem vertex_step_host_b3 : ∀ i : Fin 48, hostValue (rotateValue (144+i.val)) = hostValue (144+i.val) := by decide +kernel

private theorem vertex_step_host_b4 : ∀ i : Fin 48, hostValue (rotateValue (192+i.val)) = hostValue (192+i.val) := by decide +kernel

private theorem vertex_step_host_b5 : ∀ i : Fin 48, hostValue (rotateValue (240+i.val)) = hostValue (240+i.val) := by decide +kernel

private theorem vertex_step_host_b6 : ∀ i : Fin 48, hostValue (rotateValue (288+i.val)) = hostValue (288+i.val) := by decide +kernel

private theorem vertex_step_host_b7 : ∀ i : Fin 48, hostValue (rotateValue (336+i.val)) = hostValue (336+i.val) := by decide +kernel

private theorem vertex_step_host_b8 : ∀ i : Fin 48, hostValue (rotateValue (384+i.val)) = hostValue (384+i.val) := by decide +kernel

private theorem vertex_step_host_b9 : ∀ i : Fin 48, hostValue (rotateValue (432+i.val)) = hostValue (432+i.val) := by decide +kernel

private theorem vertex_step_host_b10 : ∀ i : Fin 48, hostValue (rotateValue (480+i.val)) = hostValue (480+i.val) := by decide +kernel

private theorem vertex_step_host_b11 : ∀ i : Fin 42, hostValue (rotateValue (528+i.val)) = hostValue (528+i.val) := by decide +kernel

private theorem vertex_step_host_n0_0 : ∀ i : Fin 96, hostValue (rotateValue (0+i.val)) = hostValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 0 48 48 vertex_step_host_b0 vertex_step_host_b1

private theorem vertex_step_host_n0_1 : ∀ i : Fin 96, hostValue (rotateValue (96+i.val)) = hostValue (96+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 96 48 48 vertex_step_host_b2 vertex_step_host_b3

private theorem vertex_step_host_n0_2 : ∀ i : Fin 96, hostValue (rotateValue (192+i.val)) = hostValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 192 48 48 vertex_step_host_b4 vertex_step_host_b5

private theorem vertex_step_host_n0_3 : ∀ i : Fin 96, hostValue (rotateValue (288+i.val)) = hostValue (288+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 288 48 48 vertex_step_host_b6 vertex_step_host_b7

private theorem vertex_step_host_n0_4 : ∀ i : Fin 96, hostValue (rotateValue (384+i.val)) = hostValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 384 48 48 vertex_step_host_b8 vertex_step_host_b9

private theorem vertex_step_host_n0_5 : ∀ i : Fin 90, hostValue (rotateValue (480+i.val)) = hostValue (480+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 480 48 42 vertex_step_host_b10 vertex_step_host_b11

private theorem vertex_step_host_n1_0 : ∀ i : Fin 192, hostValue (rotateValue (0+i.val)) = hostValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 0 96 96 vertex_step_host_n0_0 vertex_step_host_n0_1

private theorem vertex_step_host_n1_1 : ∀ i : Fin 192, hostValue (rotateValue (192+i.val)) = hostValue (192+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 192 96 96 vertex_step_host_n0_2 vertex_step_host_n0_3

private theorem vertex_step_host_n1_2 : ∀ i : Fin 186, hostValue (rotateValue (384+i.val)) = hostValue (384+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 384 96 90 vertex_step_host_n0_4 vertex_step_host_n0_5

private theorem vertex_step_host_n2_0 : ∀ i : Fin 384, hostValue (rotateValue (0+i.val)) = hostValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 0 192 192 vertex_step_host_n1_0 vertex_step_host_n1_1

private theorem vertex_step_host_n3_0 : ∀ i : Fin 570, hostValue (rotateValue (0+i.val)) = hostValue (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (rotateValue i) = hostValue i) 0 384 186 vertex_step_host_n2_0 vertex_step_host_n1_2

theorem vertex_step_host : ∀ i : Fin 570, hostValue (rotateValue i.val) = hostValue i.val := by
  simpa only [Nat.zero_add] using vertex_step_host_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
