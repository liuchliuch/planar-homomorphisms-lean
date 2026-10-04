import PlanarHom.PfaffianPivotSemantics
import PlanarHom.PfaffianEliminationTrace
import Mathlib.Algebra.Field.ZMod

open PlanarHom.MultiGraph
open PlanarHom.MultiGraph.PfaffianElimination

#print axioms supportedPfaffian_pivot
#print axioms evaluate_eq_supportedPfaffian
#print axioms evaluate_eq_pairingPfaffian
#print axioms exists_polynomial_trace_entry_bound

example (A : Matrix (Fin 0) (Fin 0) ℚ) : pairingPfaffian A = 1 := by
  rw [← evaluate_eq_pairingPfaffian A (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)]
  exact evaluate_nil A

example : pairingPfaffian (0 : Matrix (Fin 3) (Fin 3) ℚ) = 0 := by
  rw [← evaluate_eq_pairingPfaffian _ (by simp) (by simp), evaluate_zero]
  decide

example : pairingPfaffian (0 : Matrix (Fin 4) (Fin 4) ℚ) = 0 := by
  rw [← evaluate_eq_pairingPfaffian _ (by simp) (by simp), evaluate_zero]
  decide

/-- Literal signed pairing semantics for a skipped negative-parity pivot. -/
theorem literal_signed_four_vertex_regression :
    pairingPfaffian
      (![![(0 : ℚ), 0, 2, -3], ![0, 0, 5, 7],
         ![-2, -5, 0, 11], ![3, -7, -11, 0]] : Matrix (Fin 4) (Fin 4) ℚ) = -29 := by
  rw [← evaluate_eq_pairingPfaffian _ (by decide) (by decide)]
  exact signed_four_vertex_regression

/-- The semantic theorem also applies in characteristic two. -/
example (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u=0) :
    evaluate A [0,1,2,3] = pairingPfaffian A :=
  evaluate_eq_pairingPfaffian A hskew hdiag

#print axioms literal_signed_four_vertex_regression
