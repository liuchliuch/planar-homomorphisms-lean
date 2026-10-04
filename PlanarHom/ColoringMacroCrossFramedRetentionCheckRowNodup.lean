import PlanarHom.ColoringMacroCrossFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.CrossFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem row_nodup_b0 : ∀ i : Fin 48, (numericRow ⟨(0+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b1 : ∀ i : Fin 48, (numericRow ⟨(48+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b2 : ∀ i : Fin 48, (numericRow ⟨(96+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b3 : ∀ i : Fin 48, (numericRow ⟨(144+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b4 : ∀ i : Fin 48, (numericRow ⟨(192+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b5 : ∀ i : Fin 48, (numericRow ⟨(240+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b6 : ∀ i : Fin 48, (numericRow ⟨(288+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b7 : ∀ i : Fin 48, (numericRow ⟨(336+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b8 : ∀ i : Fin 48, (numericRow ⟨(384+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b9 : ∀ i : Fin 48, (numericRow ⟨(432+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b10 : ∀ i : Fin 48, (numericRow ⟨(480+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b11 : ∀ i : Fin 48, (numericRow ⟨(528+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b12 : ∀ i : Fin 48, (numericRow ⟨(576+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b13 : ∀ i : Fin 48, (numericRow ⟨(624+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b14 : ∀ i : Fin 48, (numericRow ⟨(672+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b15 : ∀ i : Fin 48, (numericRow ⟨(720+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b16 : ∀ i : Fin 48, (numericRow ⟨(768+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b17 : ∀ i : Fin 48, (numericRow ⟨(816+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b18 : ∀ i : Fin 48, (numericRow ⟨(864+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b19 : ∀ i : Fin 48, (numericRow ⟨(912+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b20 : ∀ i : Fin 48, (numericRow ⟨(960+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b21 : ∀ i : Fin 48, (numericRow ⟨(1008+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b22 : ∀ i : Fin 48, (numericRow ⟨(1056+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b23 : ∀ i : Fin 48, (numericRow ⟨(1104+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b24 : ∀ i : Fin 48, (numericRow ⟨(1152+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b25 : ∀ i : Fin 48, (numericRow ⟨(1200+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_b26 : ∀ i : Fin 26, (numericRow ⟨(1248+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by decide +kernel

private theorem row_nodup_n0_0 : ∀ i : Fin 96, (numericRow ⟨(0+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 0 48 48 row_nodup_b0 row_nodup_b1

private theorem row_nodup_n0_1 : ∀ i : Fin 96, (numericRow ⟨(96+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 96 48 48 row_nodup_b2 row_nodup_b3

private theorem row_nodup_n0_2 : ∀ i : Fin 96, (numericRow ⟨(192+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 192 48 48 row_nodup_b4 row_nodup_b5

private theorem row_nodup_n0_3 : ∀ i : Fin 96, (numericRow ⟨(288+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 288 48 48 row_nodup_b6 row_nodup_b7

private theorem row_nodup_n0_4 : ∀ i : Fin 96, (numericRow ⟨(384+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 384 48 48 row_nodup_b8 row_nodup_b9

private theorem row_nodup_n0_5 : ∀ i : Fin 96, (numericRow ⟨(480+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 480 48 48 row_nodup_b10 row_nodup_b11

private theorem row_nodup_n0_6 : ∀ i : Fin 96, (numericRow ⟨(576+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 576 48 48 row_nodup_b12 row_nodup_b13

private theorem row_nodup_n0_7 : ∀ i : Fin 96, (numericRow ⟨(672+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 672 48 48 row_nodup_b14 row_nodup_b15

private theorem row_nodup_n0_8 : ∀ i : Fin 96, (numericRow ⟨(768+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 768 48 48 row_nodup_b16 row_nodup_b17

private theorem row_nodup_n0_9 : ∀ i : Fin 96, (numericRow ⟨(864+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 864 48 48 row_nodup_b18 row_nodup_b19

private theorem row_nodup_n0_10 : ∀ i : Fin 96, (numericRow ⟨(960+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 960 48 48 row_nodup_b20 row_nodup_b21

private theorem row_nodup_n0_11 : ∀ i : Fin 96, (numericRow ⟨(1056+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 1056 48 48 row_nodup_b22 row_nodup_b23

private theorem row_nodup_n0_12 : ∀ i : Fin 96, (numericRow ⟨(1152+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 1152 48 48 row_nodup_b24 row_nodup_b25

private theorem row_nodup_n1_0 : ∀ i : Fin 192, (numericRow ⟨(0+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 0 96 96 row_nodup_n0_0 row_nodup_n0_1

private theorem row_nodup_n1_1 : ∀ i : Fin 192, (numericRow ⟨(192+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 192 96 96 row_nodup_n0_2 row_nodup_n0_3

private theorem row_nodup_n1_2 : ∀ i : Fin 192, (numericRow ⟨(384+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 384 96 96 row_nodup_n0_4 row_nodup_n0_5

private theorem row_nodup_n1_3 : ∀ i : Fin 192, (numericRow ⟨(576+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 576 96 96 row_nodup_n0_6 row_nodup_n0_7

private theorem row_nodup_n1_4 : ∀ i : Fin 192, (numericRow ⟨(768+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 768 96 96 row_nodup_n0_8 row_nodup_n0_9

private theorem row_nodup_n1_5 : ∀ i : Fin 192, (numericRow ⟨(960+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 960 96 96 row_nodup_n0_10 row_nodup_n0_11

private theorem row_nodup_n1_6 : ∀ i : Fin 122, (numericRow ⟨(1152+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 1152 96 26 row_nodup_n0_12 row_nodup_b26

private theorem row_nodup_n2_0 : ∀ i : Fin 384, (numericRow ⟨(0+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 0 192 192 row_nodup_n1_0 row_nodup_n1_1

private theorem row_nodup_n2_1 : ∀ i : Fin 384, (numericRow ⟨(384+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 384 192 192 row_nodup_n1_2 row_nodup_n1_3

private theorem row_nodup_n2_2 : ∀ i : Fin 384, (numericRow ⟨(768+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 768 192 192 row_nodup_n1_4 row_nodup_n1_5

private theorem row_nodup_n3_0 : ∀ i : Fin 768, (numericRow ⟨(0+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 0 384 384 row_nodup_n2_0 row_nodup_n2_1

private theorem row_nodup_n3_1 : ∀ i : Fin 506, (numericRow ⟨(768+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 768 384 122 row_nodup_n2_2 row_nodup_n1_6

private theorem row_nodup_n4_0 : ∀ i : Fin 1274, (numericRow ⟨(0+i.val)%1274,Nat.mod_lt _ (by decide)⟩).Nodup :=
  FiniteIntervalCheck.append (fun i => (numericRow ⟨i%1274,Nat.mod_lt _ (by decide)⟩).Nodup) 0 768 506 row_nodup_n3_0 row_nodup_n3_1

theorem row_nodup : ∀ i : Fin 1274, (numericRow ⟨i.val%1274,Nat.mod_lt _ (by decide)⟩).Nodup := by
  simpa only [Nat.zero_add] using row_nodup_n4_0

end PlanarHom.ColoringMacroFaces.CrossFramed
