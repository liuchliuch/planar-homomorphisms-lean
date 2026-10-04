import PlanarHom.ColoringMacroTestFramedFaceData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem labelBound_b0 : ∀ i : Fin 48, labelValue (0+i.val) < 169 := by decide +kernel

private theorem labelBound_b1 : ∀ i : Fin 48, labelValue (48+i.val) < 169 := by decide +kernel

private theorem labelBound_b2 : ∀ i : Fin 48, labelValue (96+i.val) < 169 := by decide +kernel

private theorem labelBound_b3 : ∀ i : Fin 48, labelValue (144+i.val) < 169 := by decide +kernel

private theorem labelBound_b4 : ∀ i : Fin 48, labelValue (192+i.val) < 169 := by decide +kernel

private theorem labelBound_b5 : ∀ i : Fin 48, labelValue (240+i.val) < 169 := by decide +kernel

private theorem labelBound_b6 : ∀ i : Fin 48, labelValue (288+i.val) < 169 := by decide +kernel

private theorem labelBound_b7 : ∀ i : Fin 48, labelValue (336+i.val) < 169 := by decide +kernel

private theorem labelBound_b8 : ∀ i : Fin 48, labelValue (384+i.val) < 169 := by decide +kernel

private theorem labelBound_b9 : ∀ i : Fin 48, labelValue (432+i.val) < 169 := by decide +kernel

private theorem labelBound_b10 : ∀ i : Fin 48, labelValue (480+i.val) < 169 := by decide +kernel

private theorem labelBound_b11 : ∀ i : Fin 42, labelValue (528+i.val) < 169 := by decide +kernel

private theorem labelBound_n0_0 : ∀ i : Fin 96, labelValue (0+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 0 48 48 labelBound_b0 labelBound_b1

private theorem labelBound_n0_1 : ∀ i : Fin 96, labelValue (96+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 96 48 48 labelBound_b2 labelBound_b3

private theorem labelBound_n0_2 : ∀ i : Fin 96, labelValue (192+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 192 48 48 labelBound_b4 labelBound_b5

private theorem labelBound_n0_3 : ∀ i : Fin 96, labelValue (288+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 288 48 48 labelBound_b6 labelBound_b7

private theorem labelBound_n0_4 : ∀ i : Fin 96, labelValue (384+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 384 48 48 labelBound_b8 labelBound_b9

private theorem labelBound_n0_5 : ∀ i : Fin 90, labelValue (480+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 480 48 42 labelBound_b10 labelBound_b11

private theorem labelBound_n1_0 : ∀ i : Fin 192, labelValue (0+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 0 96 96 labelBound_n0_0 labelBound_n0_1

private theorem labelBound_n1_1 : ∀ i : Fin 192, labelValue (192+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 192 96 96 labelBound_n0_2 labelBound_n0_3

private theorem labelBound_n1_2 : ∀ i : Fin 186, labelValue (384+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 384 96 90 labelBound_n0_4 labelBound_n0_5

private theorem labelBound_n2_0 : ∀ i : Fin 384, labelValue (0+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 0 192 192 labelBound_n1_0 labelBound_n1_1

private theorem labelBound_n3_0 : ∀ i : Fin 570, labelValue (0+i.val) < 169 :=
  FiniteIntervalCheck.append (fun i => labelValue i < 169) 0 384 186 labelBound_n2_0 labelBound_n1_2

theorem labelBound : ∀ i : Fin 570, labelValue i.val < 169 := by
  simpa only [Nat.zero_add] using labelBound_n3_0

end PlanarHom.ColoringMacroFaces.TestFramed
