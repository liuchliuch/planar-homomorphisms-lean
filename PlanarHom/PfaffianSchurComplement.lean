import PlanarHom.OccurrencePfaffianEliminationAlgorithm
import PlanarHom.PfaffianMinorHeights
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Exact Schur algebra for Pfaffian pivot elimination

The identities in this file describe the actual rational update. The matrix
congruence and bordered-minor formulas are proved algebraically. These local identities do not by themselves
identify the literal signed pairing expression with the complete evaluator.
-/
namespace PlanarHom.MultiGraph.PfaffianElimination
open scoped Matrix
variable {F : Type*} [Field F] {n : ℕ}

/-- The pivot principal two-minor is the square of the nonzero skew entry. -/
theorem pivot_principal_det (A : Matrix (Fin n) (Fin n) F) (i j : Fin n)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u = 0) :
    (A.submatrix ![i,j] ![i,j]).det = A i j ^ 2 := by
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail, hdiag, hskew i j]
  ring

/-- One actual Schur entry is a ratio of actual bordered input minors. -/
theorem pivotUpdate_eq_bordered_minor (A : Matrix (Fin n) (Fin n) F) (i j u v : Fin n)
    (hskew : ∀ a b, A b a = -A a b) (hdiag : ∀ a, A a a = 0) (hp : A i j ≠ 0) :
    pivotUpdate A i j u v =
      (A.submatrix ![i,j,u] ![i,j,v]).det / (A.submatrix ![i,j] ![i,j]).det := by
  rw [pivot_principal_det A i j hskew hdiag, Matrix.det_fin_three]
  change A u v - A i u * A j v / A i j + A j u * A i v / A i j =
    (A i i * A j j * A u v - A i i * A j v * A u j - A i j * A j i * A u v +
      A i j * A j v * A u i + A i v * A j i * A u j - A i v * A j j * A u i) / A i j ^ 2
  rw [hdiag i, hdiag j, hskew i j, hskew i u, hskew j u]
  field_simp
  <;> ring

/-- Zeroed pivot rows are genuine identities, not a storage convention. -/
theorem pivotUpdate_pivot_rows (A : Matrix (Fin n) (Fin n) F) (i j : Fin n)
    (hskew : ∀ a b, A b a = -A a b) (hdiag : ∀ a, A a a = 0) (hp : A i j ≠ 0) :
    (∀ v, pivotUpdate A i j i v = 0) ∧ (∀ v, pivotUpdate A i j j v = 0) := by
  constructor <;> intro v
  · simp only [pivotUpdate, hdiag, hskew i j]
    field_simp
    <;> ring
  · simp only [pivotUpdate, hdiag]
    field_simp
    <;> ring

end PlanarHom.MultiGraph.PfaffianElimination
