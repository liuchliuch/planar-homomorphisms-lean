import PlanarHom.CenteredLogTensorCentering
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The centered entrywise logarithm has rank exactly the number of
nondegenerate Ising factors, including the empty tensor. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CenteredLogTensorExpansion
open Boolean
variable {d : ℕ}

def characters (d : ℕ) : Matrix (Cube d) (Fin d) ℝ := fun x r=>coordinateCharacter r x

theorem characters_gram : (characters d).transpose*characters d=(2:ℝ)^d • (1:Matrix (Fin d) (Fin d) ℝ) := by
  ext r s
  simp only [Matrix.mul_apply,Matrix.transpose_apply,characters,coordinateCharacter_orthogonality,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  by_cases h:r=s <;> simp [h]

def charactersLeftInverse (d : ℕ) : Matrix (Fin d) (Cube d) ℝ :=
  ((2:ℝ)^d)⁻¹ • (characters d).transpose

theorem characters_left_inverse : charactersLeftInverse d*characters d=1 := by
  rw [charactersLeftInverse,Matrix.smul_mul,characters_gram,smul_smul]
  simp [ne_of_gt (by positivity : 0<(2:ℝ)^d)]

theorem characters_right_inverse : (characters d).transpose*(charactersLeftInverse d).transpose=1 := by
  have h := congrArg Matrix.transpose (characters_left_inverse (d:=d))
  simpa only [Matrix.transpose_mul,Matrix.transpose_one] using h

theorem weighted_outer_factorization (a : Fin d→ℝ) :
    (∑ r,a r • coordinateOuter r)=characters d*Matrix.diagonal a*(characters d).transpose := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,coordinateOuter,
    Matrix.transpose_apply,Matrix.mul_diagonal,characters]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem weighted_outer_rank (a : Fin d→ℝ) (ha : ∀ r,a r≠0) :
    (∑ r,a r • coordinateOuter r).rank=d := by
  rw [weighted_outer_factorization]
  let X := characters d
  let Y := charactersLeftInverse d
  let D := Matrix.diagonal a
  have hr : Y*(X*D*X.transpose)*Y.transpose=D := by
    calc
      Y*(X*D*X.transpose)*Y.transpose=(Y*X)*D*(X.transpose*Y.transpose) := by
        simp only [Matrix.mul_assoc]
      _=D := by rw [characters_left_inverse,characters_right_inverse,Matrix.one_mul,Matrix.mul_one]
  have hd : D.rank=d := by simp [D,Matrix.rank_diagonal,ha]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left (X*D) X.transpose).trans
      ((Matrix.rank_mul_le_left X D).trans (by simpa using Matrix.rank_le_card_width X))
  · calc
      d=D.rank := hd.symm
      _=(Y*(X*D*X.transpose)*Y.transpose).rank := congrArg Matrix.rank hr.symm
      _≤(X*D*X.transpose).rank :=
        (Matrix.rank_mul_le_left (Y*(X*D*X.transpose)) Y.transpose).trans
          (Matrix.rank_mul_le_right Y (X*D*X.transpose))

theorem centered_entrywise_log_rank (γ : ℝ) (hγ : 0<γ) (ρ : Fin d→ℝ)
    (hρ : ∀ r,0<ρ r) (hne : ∀ r,ρ r≠1) :
    (centering d*tensorLog γ ρ*centering d).rank=d := by
  rw [centered_entrywise_log γ hγ ρ hρ]
  apply weighted_outer_rank
  intro r
  exact neg_ne_zero.mpr (div_ne_zero (Real.log_ne_zero_of_pos_of_ne_one (hρ r) (hne r)) (by norm_num))

end PlanarHom.CenteredLogTensorExpansion
