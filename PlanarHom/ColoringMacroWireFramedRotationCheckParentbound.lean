import PlanarHom.ColoringMacroWireFramedRotationData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem parentBound_b0 : ∀ i : Fin 48, parentValue (0+i.val) < 534 := by decide +kernel

private theorem parentBound_b1 : ∀ i : Fin 48, parentValue (48+i.val) < 534 := by decide +kernel

private theorem parentBound_b2 : ∀ i : Fin 48, parentValue (96+i.val) < 534 := by decide +kernel

private theorem parentBound_b3 : ∀ i : Fin 48, parentValue (144+i.val) < 534 := by decide +kernel

private theorem parentBound_b4 : ∀ i : Fin 48, parentValue (192+i.val) < 534 := by decide +kernel

private theorem parentBound_b5 : ∀ i : Fin 48, parentValue (240+i.val) < 534 := by decide +kernel

private theorem parentBound_b6 : ∀ i : Fin 48, parentValue (288+i.val) < 534 := by decide +kernel

private theorem parentBound_b7 : ∀ i : Fin 48, parentValue (336+i.val) < 534 := by decide +kernel

private theorem parentBound_b8 : ∀ i : Fin 48, parentValue (384+i.val) < 534 := by decide +kernel

private theorem parentBound_b9 : ∀ i : Fin 48, parentValue (432+i.val) < 534 := by decide +kernel

private theorem parentBound_b10 : ∀ i : Fin 48, parentValue (480+i.val) < 534 := by decide +kernel

private theorem parentBound_b11 : ∀ i : Fin 6, parentValue (528+i.val) < 534 := by decide +kernel

private theorem parentBound_n0_0 : ∀ i : Fin 96, parentValue (0+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 0 48 48 parentBound_b0 parentBound_b1

private theorem parentBound_n0_1 : ∀ i : Fin 96, parentValue (96+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 96 48 48 parentBound_b2 parentBound_b3

private theorem parentBound_n0_2 : ∀ i : Fin 96, parentValue (192+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 192 48 48 parentBound_b4 parentBound_b5

private theorem parentBound_n0_3 : ∀ i : Fin 96, parentValue (288+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 288 48 48 parentBound_b6 parentBound_b7

private theorem parentBound_n0_4 : ∀ i : Fin 96, parentValue (384+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 384 48 48 parentBound_b8 parentBound_b9

private theorem parentBound_n0_5 : ∀ i : Fin 54, parentValue (480+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 480 48 6 parentBound_b10 parentBound_b11

private theorem parentBound_n1_0 : ∀ i : Fin 192, parentValue (0+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 0 96 96 parentBound_n0_0 parentBound_n0_1

private theorem parentBound_n1_1 : ∀ i : Fin 192, parentValue (192+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 192 96 96 parentBound_n0_2 parentBound_n0_3

private theorem parentBound_n1_2 : ∀ i : Fin 150, parentValue (384+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 384 96 54 parentBound_n0_4 parentBound_n0_5

private theorem parentBound_n2_0 : ∀ i : Fin 384, parentValue (0+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 0 192 192 parentBound_n1_0 parentBound_n1_1

private theorem parentBound_n3_0 : ∀ i : Fin 534, parentValue (0+i.val) < 534 :=
  FiniteIntervalCheck.append (fun i => parentValue i < 534) 0 384 150 parentBound_n2_0 parentBound_n1_2

theorem parentBound : ∀ i : Fin 534, parentValue i.val < 534 := by
  simpa only [Nat.zero_add] using parentBound_n3_0

end PlanarHom.ColoringMacroFaces.WireFramed
