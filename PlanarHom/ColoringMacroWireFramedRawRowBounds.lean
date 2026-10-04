import PlanarHom.ColoringMacroWireFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.WireFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem rawRow_all_bound_b0 : ∀ i : Fin 48, (rawRowValue (0+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b1 : ∀ i : Fin 48, (rawRowValue (48+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b2 : ∀ i : Fin 48, (rawRowValue (96+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b3 : ∀ i : Fin 48, (rawRowValue (144+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b4 : ∀ i : Fin 48, (rawRowValue (192+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b5 : ∀ i : Fin 48, (rawRowValue (240+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b6 : ∀ i : Fin 48, (rawRowValue (288+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b7 : ∀ i : Fin 48, (rawRowValue (336+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b8 : ∀ i : Fin 48, (rawRowValue (384+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b9 : ∀ i : Fin 48, (rawRowValue (432+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b10 : ∀ i : Fin 48, (rawRowValue (480+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_b11 : ∀ i : Fin 6, (rawRowValue (528+i.val)).all (fun d => decide (d<2646))=true := by decide +kernel

private theorem rawRow_all_bound_n0_0 : ∀ i : Fin 96, (rawRowValue (0+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 0 48 48 rawRow_all_bound_b0 rawRow_all_bound_b1

private theorem rawRow_all_bound_n0_1 : ∀ i : Fin 96, (rawRowValue (96+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 96 48 48 rawRow_all_bound_b2 rawRow_all_bound_b3

private theorem rawRow_all_bound_n0_2 : ∀ i : Fin 96, (rawRowValue (192+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 192 48 48 rawRow_all_bound_b4 rawRow_all_bound_b5

private theorem rawRow_all_bound_n0_3 : ∀ i : Fin 96, (rawRowValue (288+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 288 48 48 rawRow_all_bound_b6 rawRow_all_bound_b7

private theorem rawRow_all_bound_n0_4 : ∀ i : Fin 96, (rawRowValue (384+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 384 48 48 rawRow_all_bound_b8 rawRow_all_bound_b9

private theorem rawRow_all_bound_n0_5 : ∀ i : Fin 54, (rawRowValue (480+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 480 48 6 rawRow_all_bound_b10 rawRow_all_bound_b11

private theorem rawRow_all_bound_n1_0 : ∀ i : Fin 192, (rawRowValue (0+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 0 96 96 rawRow_all_bound_n0_0 rawRow_all_bound_n0_1

private theorem rawRow_all_bound_n1_1 : ∀ i : Fin 192, (rawRowValue (192+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 192 96 96 rawRow_all_bound_n0_2 rawRow_all_bound_n0_3

private theorem rawRow_all_bound_n1_2 : ∀ i : Fin 150, (rawRowValue (384+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 384 96 54 rawRow_all_bound_n0_4 rawRow_all_bound_n0_5

private theorem rawRow_all_bound_n2_0 : ∀ i : Fin 384, (rawRowValue (0+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 0 192 192 rawRow_all_bound_n1_0 rawRow_all_bound_n1_1

private theorem rawRow_all_bound_n3_0 : ∀ i : Fin 534, (rawRowValue (0+i.val)).all (fun d => decide (d<2646))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<2646))=true) 0 384 150 rawRow_all_bound_n2_0 rawRow_all_bound_n1_2

theorem rawRow_all_bound : ∀ i : Fin 534, (rawRowValue i.val).all (fun d => decide (d<2646))=true := by
  simpa only [Nat.zero_add] using rawRow_all_bound_n3_0

theorem rawRow_bound (v : Fin 534) (d : ℕ) (hd : d∈rawRowValue v.val) : d<2646 :=
  of_decide_eq_true (List.all_eq_true.mp (rawRow_all_bound v) d hd)
end PlanarHom.ColoringMacroFaces.WireFramed
