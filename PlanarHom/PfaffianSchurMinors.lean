import PlanarHom.PfaffianSchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Exact successive-Schur and bordered determinant identities. -/

noncomputable section
namespace PlanarHom.MultiGraph.PfaffianElimination
open scoped Matrix
open Matrix

section BlockAlgebra
variable {F I J V : Type*} [Field F]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]

/-- Eliminating a block and then another block equals eliminating their union. -/
theorem schur_quotient_identity
    (P : Matrix I I F) (B : Matrix I J F) (C : Matrix J I F) (D : Matrix J J F)
    (E : Matrix I V F) (T : Matrix J V F) (G : Matrix V I F) (H : Matrix V J F)
    (A : Matrix V V F) [Invertible P] [Invertible (D - C * ⅟P * B)]
    [Invertible (fromBlocks P B C D)] :
    A - fromCols G H * ⅟(fromBlocks P B C D) * fromRows E T =
      (A - G * ⅟P * E) - (H - G * ⅟P * B) * ⅟(D - C * ⅟P * B) * (T - C * ⅟P * E) := by
  rw [invOf_fromBlocks₁₁_eq, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- The full ambient residual after eliminating a selected principal block. -/
def schurResidual (A : Matrix V V F) (p : I → V) : Matrix V V F :=
  A - A.submatrix id p * (A.submatrix p p)⁻¹ * A.submatrix p id

/-- Appending selected vertices gives the literal block matrix of the original entries. -/
theorem submatrix_sum_elim (A : Matrix V V F) (p : I → V) (q : J → V) :
    A.submatrix (Sum.elim p q) (Sum.elim p q) =
      fromBlocks (A.submatrix p p) (A.submatrix p q) (A.submatrix q p) (A.submatrix q q) := by
  ext (i | i) (j | j) <;> rfl

/-- Submatrices of a Schur residual have the expected rectangular formula. -/
theorem schurResidual_submatrix {R S : Type*} (A : Matrix V V F) (p : I → V)
    (r : R → V) (s : S → V) :
    (schurResidual A p).submatrix r s =
      A.submatrix r s - A.submatrix r p * (A.submatrix p p)⁻¹ * A.submatrix p s := by
  rfl

/-- Eliminating the next principal block is exact, without assumptions on the rest of A. -/
theorem schurResidual_extend (A : Matrix V V F) (p : I → V) (q : J → V)
    [Invertible (A.submatrix p p)] [Invertible ((schurResidual A p).submatrix q q)] :
    schurResidual A (Sum.elim p q) = schurResidual (schurResidual A p) q := by
  have hs : (schurResidual A p).submatrix q q =
      A.submatrix q q - A.submatrix q p * ⅟(A.submatrix p p) * A.submatrix p q := by
    rw [schurResidual_submatrix, invOf_eq_nonsing_inv]
  letI : Invertible (A.submatrix q q - A.submatrix q p * ⅟(A.submatrix p p) * A.submatrix p q) :=
    hs ▸ inferInstance
  letI := fromBlocks₁₁Invertible (A.submatrix p p) (A.submatrix p q) (A.submatrix q p) (A.submatrix q q)
  have hc : A.submatrix id (Sum.elim p q) = fromCols (A.submatrix id p) (A.submatrix id q) := by
    ext i (j | j) <;> rfl
  have hr : A.submatrix (Sum.elim p q) id = fromRows (A.submatrix p id) (A.submatrix q id) := by
    ext (i | i) j <;> rfl
  unfold schurResidual at ⊢
  rw [submatrix_sum_elim, hc, hr, ← invOf_eq_nonsing_inv]
  rw [schur_quotient_identity]
  simp only [invOf_eq_nonsing_inv]
  rfl


/-- A bordered determinant computes one residual entry exactly. -/
theorem schurResidual_entry_minor (A : Matrix V V F) (p : I → V)
    [Invertible (A.submatrix p p)] (u v : V) :
    schurResidual A p u v =
      (A.submatrix (Sum.elim p (fun _ : Unit => u)) (Sum.elim p (fun _ : Unit => v))).det /
        (A.submatrix p p).det := by
  have hblock : A.submatrix (Sum.elim p (fun _ : Unit => u)) (Sum.elim p (fun _ : Unit => v)) =
      fromBlocks (A.submatrix p p) (A.submatrix p (fun _ : Unit => v))
        (A.submatrix (fun _ : Unit => u) p) (A.submatrix (fun _ : Unit => u) (fun _ : Unit => v)) := by
    ext (i | i) (j | j) <;> rfl
  rw [hblock, det_fromBlocks₁₁, det_unique (n := Unit), invOf_eq_nonsing_inv]
  have hd : (A.submatrix p p).det ≠ 0 := (isUnit_det_of_invertible _).ne_zero
  apply (eq_div_iff hd).mpr
  rw [mul_comm]
  rfl

/-- Empty principal elimination is exactly the original matrix. -/
@[simp] theorem schurResidual_empty (A : Matrix V V F) (p : Fin 0 → V) :
    schurResidual A p = A := by
  ext u v
  simp [schurResidual, Matrix.mul_apply]

/-- A two-vertex Schur complement is literally the materialized algorithm's update. -/
theorem schurResidual_pair (A : Matrix V V F) (i j : V)
    (hskew : ∀ a b, A b a = -A a b) (hdiag : ∀ a, A a a = 0) (hp : A i j ≠ 0) :
    schurResidual A ![i,j] = fun u v =>
      A u v - (A i u * A j v) / A i j + (A j u * A i v) / A i j := by
  have hinv : (A.submatrix ![i,j] ![i,j])⁻¹ =
      !![0, -(A i j)⁻¹; (A i j)⁻¹, 0] := by
    apply inv_eq_left_inv
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hdiag, hskew i j, hp]
  ext u v
  simp only [schurResidual, hinv, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  change A u v - ((A u i * 0 + A u j * (A i j)⁻¹) * A i v +
      (A u i * (-(A i j)⁻¹) + A u j * 0) * A j v) = _
  rw [hskew i u, hskew j u]
  simp only [div_eq_mul_inv]
  ring

/-- An appended principal block is nonsingular precisely as required by elimination. -/
theorem schurResidual_extend_det_ne_zero (A : Matrix V V F) (p : I → V) (q : J → V)
    [Invertible (A.submatrix p p)]
    (hq : ((schurResidual A p).submatrix q q).det ≠ 0) :
    (A.submatrix (Sum.elim p q) (Sum.elim p q)).det ≠ 0 := by
  rw [submatrix_sum_elim, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  exact mul_ne_zero (isUnit_det_of_invertible _).ne_zero hq

end BlockAlgebra
end PlanarHom.MultiGraph.PfaffianElimination
