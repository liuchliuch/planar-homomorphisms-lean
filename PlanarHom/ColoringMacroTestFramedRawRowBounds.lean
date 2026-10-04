import PlanarHom.ColoringMacroTestFramedRetentionData
import PlanarHom.FiniteIntervalCheck
namespace PlanarHom.ColoringMacroFaces.TestFramed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem rawRow_all_bound_b0 : ∀ i : Fin 48, (rawRowValue (0+i.val)).all (fun d => decide (d<570))=true := by decide +kernel

private theorem rawRow_all_bound_b1 : ∀ i : Fin 48, (rawRowValue (48+i.val)).all (fun d => decide (d<570))=true := by decide +kernel

private theorem rawRow_all_bound_b2 : ∀ i : Fin 22, (rawRowValue (96+i.val)).all (fun d => decide (d<570))=true := by decide +kernel

private theorem rawRow_all_bound_n0_0 : ∀ i : Fin 96, (rawRowValue (0+i.val)).all (fun d => decide (d<570))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<570))=true) 0 48 48 rawRow_all_bound_b0 rawRow_all_bound_b1

private theorem rawRow_all_bound_n1_0 : ∀ i : Fin 118, (rawRowValue (0+i.val)).all (fun d => decide (d<570))=true :=
  FiniteIntervalCheck.append (fun i => (rawRowValue i).all (fun d => decide (d<570))=true) 0 96 22 rawRow_all_bound_n0_0 rawRow_all_bound_b2

theorem rawRow_all_bound : ∀ i : Fin 118, (rawRowValue i.val).all (fun d => decide (d<570))=true := by
  simpa only [Nat.zero_add] using rawRow_all_bound_n1_0

theorem rawRow_bound (v : Fin 118) (d : ℕ) (hd : d∈rawRowValue v.val) : d<570 :=
  of_decide_eq_true (List.all_eq_true.mp (rawRow_all_bound v) d hd)
end PlanarHom.ColoringMacroFaces.TestFramed
