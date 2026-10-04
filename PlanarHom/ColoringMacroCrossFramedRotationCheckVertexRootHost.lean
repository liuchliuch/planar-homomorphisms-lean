import PlanarHom.ColoringMacroCrossFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.CrossFramed
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

private theorem vertex_root_host_b11 : ∀ i : Fin 48, hostValue (vertexRootValue (528+i.val)) = (528+i.val) := by decide +kernel

private theorem vertex_root_host_b12 : ∀ i : Fin 48, hostValue (vertexRootValue (576+i.val)) = (576+i.val) := by decide +kernel

private theorem vertex_root_host_b13 : ∀ i : Fin 48, hostValue (vertexRootValue (624+i.val)) = (624+i.val) := by decide +kernel

private theorem vertex_root_host_b14 : ∀ i : Fin 48, hostValue (vertexRootValue (672+i.val)) = (672+i.val) := by decide +kernel

private theorem vertex_root_host_b15 : ∀ i : Fin 48, hostValue (vertexRootValue (720+i.val)) = (720+i.val) := by decide +kernel

private theorem vertex_root_host_b16 : ∀ i : Fin 48, hostValue (vertexRootValue (768+i.val)) = (768+i.val) := by decide +kernel

private theorem vertex_root_host_b17 : ∀ i : Fin 48, hostValue (vertexRootValue (816+i.val)) = (816+i.val) := by decide +kernel

private theorem vertex_root_host_b18 : ∀ i : Fin 48, hostValue (vertexRootValue (864+i.val)) = (864+i.val) := by decide +kernel

private theorem vertex_root_host_b19 : ∀ i : Fin 48, hostValue (vertexRootValue (912+i.val)) = (912+i.val) := by decide +kernel

private theorem vertex_root_host_b20 : ∀ i : Fin 48, hostValue (vertexRootValue (960+i.val)) = (960+i.val) := by decide +kernel

private theorem vertex_root_host_b21 : ∀ i : Fin 48, hostValue (vertexRootValue (1008+i.val)) = (1008+i.val) := by decide +kernel

private theorem vertex_root_host_b22 : ∀ i : Fin 48, hostValue (vertexRootValue (1056+i.val)) = (1056+i.val) := by decide +kernel

private theorem vertex_root_host_b23 : ∀ i : Fin 48, hostValue (vertexRootValue (1104+i.val)) = (1104+i.val) := by decide +kernel

private theorem vertex_root_host_b24 : ∀ i : Fin 48, hostValue (vertexRootValue (1152+i.val)) = (1152+i.val) := by decide +kernel

private theorem vertex_root_host_b25 : ∀ i : Fin 48, hostValue (vertexRootValue (1200+i.val)) = (1200+i.val) := by decide +kernel

private theorem vertex_root_host_b26 : ∀ i : Fin 26, hostValue (vertexRootValue (1248+i.val)) = (1248+i.val) := by decide +kernel

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

private theorem vertex_root_host_n0_5 : ∀ i : Fin 96, hostValue (vertexRootValue (480+i.val)) = (480+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 480 48 48 vertex_root_host_b10 vertex_root_host_b11

private theorem vertex_root_host_n0_6 : ∀ i : Fin 96, hostValue (vertexRootValue (576+i.val)) = (576+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 576 48 48 vertex_root_host_b12 vertex_root_host_b13

private theorem vertex_root_host_n0_7 : ∀ i : Fin 96, hostValue (vertexRootValue (672+i.val)) = (672+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 672 48 48 vertex_root_host_b14 vertex_root_host_b15

private theorem vertex_root_host_n0_8 : ∀ i : Fin 96, hostValue (vertexRootValue (768+i.val)) = (768+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 768 48 48 vertex_root_host_b16 vertex_root_host_b17

private theorem vertex_root_host_n0_9 : ∀ i : Fin 96, hostValue (vertexRootValue (864+i.val)) = (864+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 864 48 48 vertex_root_host_b18 vertex_root_host_b19

private theorem vertex_root_host_n0_10 : ∀ i : Fin 96, hostValue (vertexRootValue (960+i.val)) = (960+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 960 48 48 vertex_root_host_b20 vertex_root_host_b21

private theorem vertex_root_host_n0_11 : ∀ i : Fin 96, hostValue (vertexRootValue (1056+i.val)) = (1056+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 1056 48 48 vertex_root_host_b22 vertex_root_host_b23

private theorem vertex_root_host_n0_12 : ∀ i : Fin 96, hostValue (vertexRootValue (1152+i.val)) = (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 1152 48 48 vertex_root_host_b24 vertex_root_host_b25

private theorem vertex_root_host_n1_0 : ∀ i : Fin 192, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 96 96 vertex_root_host_n0_0 vertex_root_host_n0_1

private theorem vertex_root_host_n1_1 : ∀ i : Fin 192, hostValue (vertexRootValue (192+i.val)) = (192+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 192 96 96 vertex_root_host_n0_2 vertex_root_host_n0_3

private theorem vertex_root_host_n1_2 : ∀ i : Fin 192, hostValue (vertexRootValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 384 96 96 vertex_root_host_n0_4 vertex_root_host_n0_5

private theorem vertex_root_host_n1_3 : ∀ i : Fin 192, hostValue (vertexRootValue (576+i.val)) = (576+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 576 96 96 vertex_root_host_n0_6 vertex_root_host_n0_7

private theorem vertex_root_host_n1_4 : ∀ i : Fin 192, hostValue (vertexRootValue (768+i.val)) = (768+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 768 96 96 vertex_root_host_n0_8 vertex_root_host_n0_9

private theorem vertex_root_host_n1_5 : ∀ i : Fin 192, hostValue (vertexRootValue (960+i.val)) = (960+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 960 96 96 vertex_root_host_n0_10 vertex_root_host_n0_11

private theorem vertex_root_host_n1_6 : ∀ i : Fin 122, hostValue (vertexRootValue (1152+i.val)) = (1152+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 1152 96 26 vertex_root_host_n0_12 vertex_root_host_b26

private theorem vertex_root_host_n2_0 : ∀ i : Fin 384, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 192 192 vertex_root_host_n1_0 vertex_root_host_n1_1

private theorem vertex_root_host_n2_1 : ∀ i : Fin 384, hostValue (vertexRootValue (384+i.val)) = (384+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 384 192 192 vertex_root_host_n1_2 vertex_root_host_n1_3

private theorem vertex_root_host_n2_2 : ∀ i : Fin 384, hostValue (vertexRootValue (768+i.val)) = (768+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 768 192 192 vertex_root_host_n1_4 vertex_root_host_n1_5

private theorem vertex_root_host_n3_0 : ∀ i : Fin 768, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 384 384 vertex_root_host_n2_0 vertex_root_host_n2_1

private theorem vertex_root_host_n3_1 : ∀ i : Fin 506, hostValue (vertexRootValue (768+i.val)) = (768+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 768 384 122 vertex_root_host_n2_2 vertex_root_host_n1_6

private theorem vertex_root_host_n4_0 : ∀ i : Fin 1274, hostValue (vertexRootValue (0+i.val)) = (0+i.val) :=
  FiniteIntervalCheck.append (fun i => hostValue (vertexRootValue i) = i) 0 768 506 vertex_root_host_n3_0 vertex_root_host_n3_1

theorem vertex_root_host : ∀ i : Fin 1274, hostValue (vertexRootValue i.val) = i.val := by
  simpa only [Nat.zero_add] using vertex_root_host_n4_0

end PlanarHom.ColoringMacroFaces.CrossFramed
