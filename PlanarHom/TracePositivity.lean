import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith

/-! # Positive trace terms for the noncommutative exponential Hessian -/

open scoped BigOperators MatrixOrder
open Matrix
noncomputable section

namespace PlanarHom.TracePositivity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Products of two PSD matrices have nonnegative trace; the product itself
need not be Hermitian or positive semidefinite. -/
theorem trace_mul_nonneg {A B : Matrix V V ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  let S := CFC.sqrt B
  have hS : S.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hs : S * S = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hp := (hA.mul_mul_conjTranspose_same S).trace_nonneg
  rw [hS.eq] at hp
  calc
    0 ≤ (S * A * S).trace := hp
    _ = (A * (S * S)).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_assoc]
    _ = (A * B).trace := by rw [hs]

/-- The individual cyclic trace terms in the exponential derivative are
nonnegative at a PSD base point and a Hermitian direction. -/
theorem trace_pow_mul_direction_nonneg {B D : Matrix V V ℝ}
    (hB : B.PosSemidef) (hD : D.IsHermitian) (k l : ℕ) :
    0 ≤ (B ^ k * D * B ^ l * D).trace := by
  have hQ : (D * B ^ l * D).PosSemidef := by
    simpa only [hD.eq] using (hB.pow l).conjTranspose_mul_mul_same D
  simpa only [Matrix.mul_assoc] using trace_mul_nonneg (hB.pow k) hQ

omit [DecidableEq V] in
/-- The zeroth cyclic term is strictly positive for a nonzero Hermitian
real direction, including all degenerate dimension cases vacuously. -/
theorem trace_direction_sq_pos {D : Matrix V V ℝ}
    (hD : D.IsHermitian) (hne : D ≠ 0) : 0 < (D * D).trace := by
  have hnonneg : 0 ≤ (D * D).trace := by
    simpa only [hD.eq] using (Matrix.posSemidef_conjTranspose_mul_self D).trace_nonneg
  have hnz : (D * D).trace ≠ 0 := by
    simpa only [hD.eq] using
      (Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := D)).not.mpr hne
  exact lt_of_le_of_ne hnonneg (Ne.symm hnz)

/-- Every real Hermitian matrix has a nonnegative scalar identity shift that
is PSD. The explicit shift is the sum of absolute eigenvalues. -/
theorem exists_nonneg_scalar_shift_posSemidef {A : Matrix V V ℝ}
    (hA : A.IsHermitian) : ∃ a : ℝ, 0 ≤ a ∧ (A + a • (1 : Matrix V V ℝ)).PosSemidef := by
  let a : ℝ := ∑ i, |hA.eigenvalues i|
  have ha : 0 ≤ a := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hshiftEigen (i : V) : 0 ≤ hA.eigenvalues i + a := by
    have hi : |hA.eigenvalues i| ≤ a :=
      Finset.single_le_sum (fun j _ => abs_nonneg (hA.eigenvalues j)) (Finset.mem_univ i)
    have hl := neg_abs_le (hA.eigenvalues i)
    linarith
  let U : Matrix V V ℝ := hA.eigenvectorUnitary
  have hU : U * Uᴴ = 1 := unitary.coe_mul_star_self hA.eigenvectorUnitary
  have he : A = U * Matrix.diagonal hA.eigenvalues * Uᴴ := by
    simpa [U, Function.comp_def] using hA.spectral_theorem
  have hd : Matrix.diagonal (fun i => hA.eigenvalues i + a) =
      Matrix.diagonal hA.eigenvalues + a • (1 : Matrix V V ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hs : U * Matrix.diagonal (fun i => hA.eigenvalues i + a) * Uᴴ =
      A + a • (1 : Matrix V V ℝ) := by
    rw [hd, Matrix.mul_add, Matrix.add_mul, ← he, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU]
  refine ⟨a, ha, ?_⟩
  rw [← hs]
  exact (Matrix.posSemidef_diagonal_iff.mpr hshiftEigen).mul_mul_conjTranspose_same U

end PlanarHom.TracePositivity
