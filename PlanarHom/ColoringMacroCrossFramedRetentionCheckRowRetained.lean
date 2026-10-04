import PlanarHom.ColoringMacroCrossFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.CrossFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_retained_b0 : ∀ i : Fin 48, retainedRawRow ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b1 : ∀ i : Fin 48, retainedRawRow ⟨(48+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(48+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b2 : ∀ i : Fin 48, retainedRawRow ⟨(96+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(96+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b3 : ∀ i : Fin 48, retainedRawRow ⟨(144+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(144+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b4 : ∀ i : Fin 48, retainedRawRow ⟨(192+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(192+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b5 : ∀ i : Fin 48, retainedRawRow ⟨(240+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(240+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b6 : ∀ i : Fin 48, retainedRawRow ⟨(288+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(288+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b7 : ∀ i : Fin 48, retainedRawRow ⟨(336+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(336+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b8 : ∀ i : Fin 48, retainedRawRow ⟨(384+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(384+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b9 : ∀ i : Fin 48, retainedRawRow ⟨(432+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(432+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b10 : ∀ i : Fin 48, retainedRawRow ⟨(480+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(480+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b11 : ∀ i : Fin 48, retainedRawRow ⟨(528+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(528+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b12 : ∀ i : Fin 48, retainedRawRow ⟨(576+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(576+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b13 : ∀ i : Fin 48, retainedRawRow ⟨(624+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(624+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b14 : ∀ i : Fin 48, retainedRawRow ⟨(672+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(672+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b15 : ∀ i : Fin 48, retainedRawRow ⟨(720+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(720+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b16 : ∀ i : Fin 48, retainedRawRow ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b17 : ∀ i : Fin 48, retainedRawRow ⟨(816+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(816+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b18 : ∀ i : Fin 48, retainedRawRow ⟨(864+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(864+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b19 : ∀ i : Fin 48, retainedRawRow ⟨(912+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(912+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b20 : ∀ i : Fin 48, retainedRawRow ⟨(960+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(960+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b21 : ∀ i : Fin 48, retainedRawRow ⟨(1008+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1008+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b22 : ∀ i : Fin 48, retainedRawRow ⟨(1056+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1056+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b23 : ∀ i : Fin 48, retainedRawRow ⟨(1104+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1104+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b24 : ∀ i : Fin 48, retainedRawRow ⟨(1152+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1152+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b25 : ∀ i : Fin 48, retainedRawRow ⟨(1200+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1200+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_b26 : ∀ i : Fin 22, retainedRawRow ⟨(1248+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1248+i.val)%1270,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem row_retained_n0_0 : ∀ i : Fin 96, retainedRawRow ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 0 48 48 row_retained_b0 row_retained_b1

private theorem row_retained_n0_1 : ∀ i : Fin 96, retainedRawRow ⟨(96+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(96+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 96 48 48 row_retained_b2 row_retained_b3

private theorem row_retained_n0_2 : ∀ i : Fin 96, retainedRawRow ⟨(192+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(192+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 192 48 48 row_retained_b4 row_retained_b5

private theorem row_retained_n0_3 : ∀ i : Fin 96, retainedRawRow ⟨(288+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(288+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 288 48 48 row_retained_b6 row_retained_b7

private theorem row_retained_n0_4 : ∀ i : Fin 96, retainedRawRow ⟨(384+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(384+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 384 48 48 row_retained_b8 row_retained_b9

private theorem row_retained_n0_5 : ∀ i : Fin 96, retainedRawRow ⟨(480+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(480+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 480 48 48 row_retained_b10 row_retained_b11

private theorem row_retained_n0_6 : ∀ i : Fin 96, retainedRawRow ⟨(576+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(576+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 576 48 48 row_retained_b12 row_retained_b13

private theorem row_retained_n0_7 : ∀ i : Fin 96, retainedRawRow ⟨(672+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(672+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 672 48 48 row_retained_b14 row_retained_b15

private theorem row_retained_n0_8 : ∀ i : Fin 96, retainedRawRow ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 768 48 48 row_retained_b16 row_retained_b17

private theorem row_retained_n0_9 : ∀ i : Fin 96, retainedRawRow ⟨(864+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(864+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 864 48 48 row_retained_b18 row_retained_b19

private theorem row_retained_n0_10 : ∀ i : Fin 96, retainedRawRow ⟨(960+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(960+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 960 48 48 row_retained_b20 row_retained_b21

private theorem row_retained_n0_11 : ∀ i : Fin 96, retainedRawRow ⟨(1056+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1056+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 1056 48 48 row_retained_b22 row_retained_b23

private theorem row_retained_n0_12 : ∀ i : Fin 96, retainedRawRow ⟨(1152+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1152+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 1152 48 48 row_retained_b24 row_retained_b25

private theorem row_retained_n1_0 : ∀ i : Fin 192, retainedRawRow ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 0 96 96 row_retained_n0_0 row_retained_n0_1

private theorem row_retained_n1_1 : ∀ i : Fin 192, retainedRawRow ⟨(192+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(192+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 192 96 96 row_retained_n0_2 row_retained_n0_3

private theorem row_retained_n1_2 : ∀ i : Fin 192, retainedRawRow ⟨(384+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(384+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 384 96 96 row_retained_n0_4 row_retained_n0_5

private theorem row_retained_n1_3 : ∀ i : Fin 192, retainedRawRow ⟨(576+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(576+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 576 96 96 row_retained_n0_6 row_retained_n0_7

private theorem row_retained_n1_4 : ∀ i : Fin 192, retainedRawRow ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 768 96 96 row_retained_n0_8 row_retained_n0_9

private theorem row_retained_n1_5 : ∀ i : Fin 192, retainedRawRow ⟨(960+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(960+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 960 96 96 row_retained_n0_10 row_retained_n0_11

private theorem row_retained_n1_6 : ∀ i : Fin 118, retainedRawRow ⟨(1152+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(1152+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 1152 96 22 row_retained_n0_12 row_retained_b26

private theorem row_retained_n2_0 : ∀ i : Fin 384, retainedRawRow ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 0 192 192 row_retained_n1_0 row_retained_n1_1

private theorem row_retained_n2_1 : ∀ i : Fin 384, retainedRawRow ⟨(384+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(384+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 384 192 192 row_retained_n1_2 row_retained_n1_3

private theorem row_retained_n2_2 : ∀ i : Fin 384, retainedRawRow ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 768 192 192 row_retained_n1_4 row_retained_n1_5

private theorem row_retained_n3_0 : ∀ i : Fin 768, retainedRawRow ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 0 384 384 row_retained_n2_0 row_retained_n2_1

private theorem row_retained_n3_1 : ∀ i : Fin 502, retainedRawRow ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(768+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 768 384 118 row_retained_n2_2 row_retained_n1_6

private theorem row_retained_n4_0 : ∀ i : Fin 1270, retainedRawRow ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨(0+i.val)%1270,Nat.mod_lt _ (by decide)⟩ :=
  FiniteIntervalCheck.append (fun i => retainedRawRow ⟨i%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i%1270,Nat.mod_lt _ (by decide)⟩) 0 768 502 row_retained_n3_0 row_retained_n3_1

theorem row_retained : ∀ i : Fin 1270, retainedRawRow ⟨i.val%1270,Nat.mod_lt _ (by decide)⟩=ColoringCrossMacroRows.raw ⟨i.val%1270,Nat.mod_lt _ (by decide)⟩ := by
  simpa only [Nat.zero_add] using row_retained_n4_0

end PlanarHom.ColoringMacroFaces.CrossFramed
