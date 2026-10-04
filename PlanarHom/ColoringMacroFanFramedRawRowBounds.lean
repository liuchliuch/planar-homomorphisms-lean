import PlanarHom.ColoringMacroFanFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.FanFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem rawRow_all_bound_b0 : ∀ i : Fin 48, (rawRowValue (0+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b1 : ∀ i : Fin 48, (rawRowValue (48+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b2 : ∀ i : Fin 48, (rawRowValue (96+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b3 : ∀ i : Fin 48, (rawRowValue (144+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b4 : ∀ i : Fin 48, (rawRowValue (192+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b5 : ∀ i : Fin 48, (rawRowValue (240+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b6 : ∀ i : Fin 48, (rawRowValue (288+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b7 : ∀ i : Fin 48, (rawRowValue (336+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b8 : ∀ i : Fin 48, (rawRowValue (384+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b9 : ∀ i : Fin 48, (rawRowValue (432+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b10 : ∀ i : Fin 48, (rawRowValue (480+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b11 : ∀ i : Fin 48, (rawRowValue (528+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b12 : ∀ i : Fin 48, (rawRowValue (576+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b13 : ∀ i : Fin 48, (rawRowValue (624+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b14 : ∀ i : Fin 48, (rawRowValue (672+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b15 : ∀ i : Fin 48, (rawRowValue (720+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b16 : ∀ i : Fin 48, (rawRowValue (768+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b17 : ∀ i : Fin 48, (rawRowValue (816+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b18 : ∀ i : Fin 48, (rawRowValue (864+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b19 : ∀ i : Fin 48, (rawRowValue (912+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b20 : ∀ i : Fin 48, (rawRowValue (960+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b21 : ∀ i : Fin 48, (rawRowValue (1008+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_b22 : ∀ i : Fin 2, (rawRowValue (1056+i.val)).all (fun d => decide (d<5264))=true := by decide +kernel

private theorem rawRow_all_bound_n0_0 : ∀ i : Fin 96, (rawRowValue (0+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 0 48 48 rawRow_all_bound_b0 rawRow_all_bound_b1

private theorem rawRow_all_bound_n0_1 : ∀ i : Fin 96, (rawRowValue (96+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 96 48 48 rawRow_all_bound_b2 rawRow_all_bound_b3

private theorem rawRow_all_bound_n0_2 : ∀ i : Fin 96, (rawRowValue (192+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 192 48 48 rawRow_all_bound_b4 rawRow_all_bound_b5

private theorem rawRow_all_bound_n0_3 : ∀ i : Fin 96, (rawRowValue (288+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 288 48 48 rawRow_all_bound_b6 rawRow_all_bound_b7

private theorem rawRow_all_bound_n0_4 : ∀ i : Fin 96, (rawRowValue (384+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 384 48 48 rawRow_all_bound_b8 rawRow_all_bound_b9

private theorem rawRow_all_bound_n0_5 : ∀ i : Fin 96, (rawRowValue (480+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 480 48 48 rawRow_all_bound_b10 rawRow_all_bound_b11

private theorem rawRow_all_bound_n0_6 : ∀ i : Fin 96, (rawRowValue (576+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 576 48 48 rawRow_all_bound_b12 rawRow_all_bound_b13

private theorem rawRow_all_bound_n0_7 : ∀ i : Fin 96, (rawRowValue (672+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 672 48 48 rawRow_all_bound_b14 rawRow_all_bound_b15

private theorem rawRow_all_bound_n0_8 : ∀ i : Fin 96, (rawRowValue (768+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 768 48 48 rawRow_all_bound_b16 rawRow_all_bound_b17

private theorem rawRow_all_bound_n0_9 : ∀ i : Fin 96, (rawRowValue (864+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 864 48 48 rawRow_all_bound_b18 rawRow_all_bound_b19

private theorem rawRow_all_bound_n0_10 : ∀ i : Fin 96, (rawRowValue (960+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 960 48 48 rawRow_all_bound_b20 rawRow_all_bound_b21

private theorem rawRow_all_bound_n1_0 : ∀ i : Fin 192, (rawRowValue (0+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 0 96 96 rawRow_all_bound_n0_0 rawRow_all_bound_n0_1

private theorem rawRow_all_bound_n1_1 : ∀ i : Fin 192, (rawRowValue (192+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 192 96 96 rawRow_all_bound_n0_2 rawRow_all_bound_n0_3

private theorem rawRow_all_bound_n1_2 : ∀ i : Fin 192, (rawRowValue (384+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 384 96 96 rawRow_all_bound_n0_4 rawRow_all_bound_n0_5

private theorem rawRow_all_bound_n1_3 : ∀ i : Fin 192, (rawRowValue (576+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 576 96 96 rawRow_all_bound_n0_6 rawRow_all_bound_n0_7

private theorem rawRow_all_bound_n1_4 : ∀ i : Fin 192, (rawRowValue (768+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 768 96 96 rawRow_all_bound_n0_8 rawRow_all_bound_n0_9

private theorem rawRow_all_bound_n1_5 : ∀ i : Fin 98, (rawRowValue (960+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 960 96 2 rawRow_all_bound_n0_10 rawRow_all_bound_b22

private theorem rawRow_all_bound_n2_0 : ∀ i : Fin 384, (rawRowValue (0+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 0 192 192 rawRow_all_bound_n1_0 rawRow_all_bound_n1_1

private theorem rawRow_all_bound_n2_1 : ∀ i : Fin 384, (rawRowValue (384+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 384 192 192 rawRow_all_bound_n1_2 rawRow_all_bound_n1_3

private theorem rawRow_all_bound_n2_2 : ∀ i : Fin 290, (rawRowValue (768+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 768 192 98 rawRow_all_bound_n1_4 rawRow_all_bound_n1_5

private theorem rawRow_all_bound_n3_0 : ∀ i : Fin 768, (rawRowValue (0+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 0 384 384 rawRow_all_bound_n2_0 rawRow_all_bound_n2_1

private theorem rawRow_all_bound_n4_0 : ∀ i : Fin 1058, (rawRowValue (0+i.val)).all (fun d => decide (d<5264))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<5264))=true) 0 768 290 rawRow_all_bound_n3_0 rawRow_all_bound_n2_2

theorem rawRow_all_bound : ∀ i : Fin 1058, (rawRowValue i.val).all (fun d => decide (d<5264))=true := by
  simpa only [Nat.zero_add] using rawRow_all_bound_n4_0

theorem rawRow_bound (v : Fin 1058) (d : ℕ) (hd : d∈rawRowValue v.val) : d<5264 :=
  of_decide_eq_true (List.all_eq_true.mp (rawRow_all_bound v) d hd)
end PlanarHom.ColoringMacroFaces.FanFramed
