import PlanarHom.Boolean
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

/-!
# Nonsingularity and positive definiteness of Boolean Ising tensors

This file interprets the entrywise Boolean tensors as matrices. Walsh
orthogonality gives a genuine diagonalization, determinant formula and
nonsingularity. Positive parameters different from one give independent,
nonproportional rows; parameters in `(0,1)` give positive-definite matrices.
-/

noncomputable section

namespace PlanarHom.Boolean

open scoped BigOperators ComplexOrder
open Matrix

/-- The unnormalized real Walsh matrix. -/
def walshMatrix (d : ℕ) : Matrix (Cube d) (Cube d) ℝ := character

theorem walshMatrix_symm (d : ℕ) : (walshMatrix d)ᵀ = walshMatrix d := by
  ext x y
  exact character_symm y x

theorem walshMatrix_isHermitian (d : ℕ) : (walshMatrix d).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, star_trivial, walshMatrix]
  exact character_symm y x

/-- Walsh orthogonality as a matrix product. -/
theorem walshMatrix_mul_self (d : ℕ) :
    walshMatrix d * walshMatrix d = (2 : ℝ) ^ d • (1 : Matrix (Cube d) (Cube d) ℝ) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, walshMatrix, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp_rw [character_symm _ y]
  rw [character_orthogonality]
  split_ifs <;> simp

/-- The Walsh transform is injective in every dimension, including zero. -/
theorem walshMatrix_mulVec_injective (d : ℕ) :
    Function.Injective (walshMatrix d).mulVec := by
  intro f g h
  have h' := congrArg (walshMatrix d).mulVec h
  simp only [Matrix.mulVec_mulVec, walshMatrix_mul_self, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h'
  exact (smul_right_injective _ (pow_ne_zero d (by norm_num : (2 : ℝ) ≠ 0))) h'

/-- Multiplication by the Walsh matrix diagonalizes the Boolean tensor. -/
theorem tensor_mul_walshMatrix {d : ℕ} (ρ : Fin d → ℝ) :
    Matrix.of (tensor ρ) * walshMatrix d =
      walshMatrix d * Matrix.diagonal (eigenvalue ρ) := by
  classical
  ext x s
  simp only [Matrix.mul_apply, Matrix.of_apply, walshMatrix]
  simp_rw [character_symm _ s]
  rw [tensor_character]
  simp [Matrix.diagonal, mul_comm, character_symm s x]

/-- The determinant is the product of the Walsh eigenvalues. -/
theorem tensor_det {d : ℕ} (ρ : Fin d → ℝ) :
    Matrix.det (Matrix.of (tensor ρ)) = ∏ s : Cube d, eigenvalue ρ s := by
  have h := congrArg Matrix.det (tensor_mul_walshMatrix ρ)
  simp only [Matrix.det_mul, Matrix.det_diagonal] at h
  have hW : Matrix.det (walshMatrix d) ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _ |>.mp
      (Matrix.mulVec_injective_iff_isUnit.mp (walshMatrix_mulVec_injective d))).ne_zero
  exact mul_right_cancel₀ hW (h.trans (mul_comm _ _))

/-- No Walsh eigenvalue vanishes when all parameters are positive and unequal to one. -/
theorem eigenvalue_ne_zero {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hne : ∀ i, ρ i ≠ 1) (s : Cube d) :
    eigenvalue ρ s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases s i
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    exact ne_of_gt (by linarith [hpos i])
  · simp only [↓reduceIte, neg_one_mul]
    intro h
    apply hne i
    linarith

/-- Strictly positive parameters different from one give a nonsingular matrix. -/
theorem tensor_det_ne_zero {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hne : ∀ i, ρ i ≠ 1) :
    Matrix.det (Matrix.of (tensor ρ)) ≠ 0 := by
  rw [tensor_det]
  exact Finset.prod_ne_zero_iff.mpr fun s _ => eigenvalue_ne_zero hpos hne s

/-- Algebraic invertibility in the matrix ring. -/
theorem tensor_isUnit {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hne : ∀ i, ρ i ≠ 1) :
    IsUnit (Matrix.of (tensor ρ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact tensor_det_ne_zero hpos hne

/-- The tensor's multiplication map has trivial kernel. -/
theorem tensor_mulVec_injective {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hne : ∀ i, ρ i ≠ 1) :
    Function.Injective (Matrix.mulVec (tensor ρ)) :=
  Matrix.mulVec_injective_iff_isUnit.mpr (tensor_isUnit hpos hne)

/-- The rows are linearly independent over the reals. -/
theorem tensor_rows_linearIndependent {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hne : ∀ i, ρ i ≠ 1) :
    LinearIndependent ℝ (tensor ρ) :=
  Matrix.linearIndependent_rows_iff_isUnit.mpr (tensor_isUnit hpos hne)

/-- Distinct Boolean states give nonproportional rows, even allowing zero scalars. -/
theorem tensor_rows_not_proportional {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hne : ∀ i, ρ i ≠ 1)
    {x y : Cube d} (hxy : x ≠ y) (c : ℝ) :
    tensor ρ x ≠ c • tensor ρ y := by
  intro h
  apply hxy
  exact (tensor_rows_linearIndependent hpos hne).eq_of_smul_apply_eq_smul_apply
    1 c x y one_ne_zero (by simpa only [one_smul] using h)

/-- In particular, all rows of a nondegenerate positive tensor are distinct. -/
theorem tensor_rows_injective {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hne : ∀ i, ρ i ≠ 1) :
    Function.Injective (tensor ρ) :=
  (tensor_rows_linearIndependent hpos hne).injective

/-- Parameters in the open unit interval give strictly positive Walsh eigenvalues. -/
theorem eigenvalue_pos {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hlt : ∀ i, ρ i < 1) (s : Cube d) :
    0 < eigenvalue ρ s := by
  apply Finset.prod_pos
  intro i _
  cases s i <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  · linarith [hpos i]
  · linarith [hlt i]

/-- Reconstructing the tensor from its diagonal Walsh spectrum. -/
theorem walshMatrix_diagonal_mul {d : ℕ} (ρ : Fin d → ℝ) :
    walshMatrix d * Matrix.diagonal (eigenvalue ρ) * walshMatrix d =
      (2 : ℝ) ^ d • Matrix.of (tensor ρ) := by
  rw [← tensor_mul_walshMatrix, Matrix.mul_assoc, walshMatrix_mul_self,
    Matrix.mul_smul, Matrix.mul_one]

/-- The real Boolean Ising tensor is positive definite for parameters in `(0,1)`. -/
theorem tensor_posDef {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hlt : ∀ i, ρ i < 1) :
    Matrix.PosDef (tensor ρ) := by
  classical
  have hD := Matrix.PosDef.diagonal (eigenvalue_pos hpos hlt)
  have hH := hD.conjTranspose_mul_mul_same (walshMatrix_mulVec_injective d)
  have hscaled : ((2 : ℝ) ^ d • Matrix.of (tensor ρ)).PosDef := by
    simpa only [(walshMatrix_isHermitian d).eq, walshMatrix_diagonal_mul] using hH
  have hN : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) d
  simpa only [smul_smul, inv_mul_cancel₀ hN.ne', one_smul] using
    hscaled.smul (inv_pos.mpr hN)

/-- One Ising factor cancels its sign-reversed partner up to its determinant. -/
theorem W_mul_neg (ρ : ℝ) (x y : Bool) :
    (∑ z : Bool, W ρ x z * W (-ρ) z y) = if x = y then 1 - ρ ^ 2 else 0 := by
  cases x <;> cases y <;> simp [W] <;> ring

/-- A tensor times its sign-reversed tensor is a scalar identity matrix. -/
theorem tensor_mul_neg {d : ℕ} (ρ : Fin d → ℝ) :
    Matrix.of (tensor ρ) * Matrix.of (tensor (fun i => -ρ i)) =
      (∏ i, (1 - (ρ i) ^ 2)) • (1 : Matrix (Cube d) (Cube d) ℝ) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.of_apply, tensor, ← Finset.prod_mul_distrib,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [← Fintype.prod_sum (fun (i : Fin d) (z : Bool) =>
    W (ρ i) (x i) z * W (-ρ i) z (y i))]
  simp_rw [W_mul_neg, Fintype.prod_ite_zero]
  by_cases h : x = y
  · subst y
    simp
  · have h' : ¬∀ i, x i = y i := fun hf => h (funext hf)
    simp [h, h']

/-- The explicit inverse is the sign-reversed tensor divided by `∏ᵢ(1-ρᵢ²)`. -/
theorem tensor_inv {d : ℕ} {ρ : Fin d → ℝ}
    (h : ∀ i, (ρ i) ^ 2 ≠ 1) :
    (Matrix.of (tensor ρ))⁻¹ =
      (∏ i, (1 - (ρ i) ^ 2))⁻¹ • Matrix.of (tensor (fun i => -ρ i)) := by
  have hprod : (∏ i, (1 - (ρ i) ^ 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (h i).symm
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, tensor_mul_neg, smul_smul, inv_mul_cancel₀ hprod, one_smul]

/-- Positive non-unit parameters meet the explicit inverse formula's hypotheses. -/
theorem tensor_inv_of_pos {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hne : ∀ i, ρ i ≠ 1) :
    (Matrix.of (tensor ρ))⁻¹ =
      (∏ i, (1 - (ρ i) ^ 2))⁻¹ • Matrix.of (tensor (fun i => -ρ i)) := by
  apply tensor_inv
  intro i hi
  apply hne i
  have hfactor : (ρ i - 1) * (ρ i + 1) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (by linarith [hpos i]))

/-- The exact singularity criterion for arbitrary real parameters. -/
theorem tensor_det_ne_zero_iff {d : ℕ} (ρ : Fin d → ℝ) :
    Matrix.det (Matrix.of (tensor ρ)) ≠ 0 ↔ ∀ i, (ρ i) ^ 2 ≠ 1 := by
  constructor
  · intro h i
    rw [tensor_det, Finset.prod_ne_zero_iff] at h
    have hplus := h (fun _ => false) (Finset.mem_univ _)
    have hminus := h (fun _ => true) (Finset.mem_univ _)
    simp only [eigenvalue, Bool.false_eq_true, ↓reduceIte, one_mul,
      Finset.prod_ne_zero_iff] at hplus
    simp only [eigenvalue, ↓reduceIte, neg_one_mul,
      Finset.prod_ne_zero_iff] at hminus
    rw [sq_ne_one_iff]
    constructor
    · intro hi
      exact hminus i (Finset.mem_univ i) (by simp [hi])
    · intro hi
      exact hplus i (Finset.mem_univ i) (by simp [hi])
  · intro h
    have hprod : (∏ i, (1 - (ρ i) ^ 2)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (h i).symm
    apply Matrix.det_ne_zero_of_right_inverse (B :=
      (∏ i, (1 - (ρ i) ^ 2))⁻¹ • Matrix.of (tensor (fun i => -ρ i)))
    rw [Matrix.mul_smul, tensor_mul_neg, smul_smul, inv_mul_cancel₀ hprod, one_smul]

/-- Exact invertibility, expressed in the matrix ring rather than through a wrapper. -/
theorem tensor_isUnit_iff {d : ℕ} (ρ : Fin d → ℝ) :
    IsUnit (Matrix.of (tensor ρ)) ↔ ∀ i, (ρ i) ^ 2 ≠ 1 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, tensor_det_ne_zero_iff]

/-- With positive parameters the only singular factors are those equal to one. -/
theorem tensor_isUnit_iff_of_pos {d : ℕ} {ρ : Fin d → ℝ}
    (hpos : ∀ i, 0 < ρ i) :
    IsUnit (Matrix.of (tensor ρ)) ↔ ∀ i, ρ i ≠ 1 := by
  rw [tensor_isUnit_iff]
  constructor
  · intro h i
    exact (sq_ne_one_iff.mp (h i)).1
  · intro h i
    exact sq_ne_one_iff.mpr ⟨h i, by linarith [hpos i]⟩

end PlanarHom.Boolean
