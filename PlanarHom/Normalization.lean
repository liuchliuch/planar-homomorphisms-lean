import PlanarHom.Quotient
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Positive diagonal normalization

Algebraic row facts used in Lemma 8.2 and the normalization/actual-twin arguments
in Sections 8 and 11. No gadget-availability or complexity conclusion is made.
-/

namespace PlanarHom

variable {C : Type*}

/-- Normalize each edge by the square roots of its two diagonal values. -/
noncomputable def diagonalNormalize (M : Matrix C C ℝ) : Matrix C C ℝ :=
  fun i j => M i j / (Real.sqrt (M i i) * Real.sqrt (M j j))

theorem diagonalNormalize_symmetric (M : Matrix C C ℝ)
    (hM : ∀ i j, M i j = M j i) :
    ∀ i j, diagonalNormalize M i j = diagonalNormalize M j i := by
  intro i j
  simp only [diagonalNormalize, hM i j, mul_comm]

theorem diagonalNormalize_diagonal (M : Matrix C C ℝ) (hd : ∀ i, 0 < M i i) (i : C) :
    diagonalNormalize M i i = 1 := by
  rw [diagonalNormalize, Real.mul_self_sqrt (hd i).le, div_self (hd i).ne']

theorem diagonalNormalize_positive (M : Matrix C C ℝ) (hM : ∀ i j, 0 < M i j) :
    ∀ i j, 0 < diagonalNormalize M i j := by
  intro i j
  exact div_pos (hM i j) (mul_pos (Real.sqrt_pos.2 (hM i i)) (Real.sqrt_pos.2 (hM j j)))

theorem diagonalNormalize_recover (M : Matrix C C ℝ) (hd : ∀ i, 0 < M i i) (i j : C) :
    M i j = (Real.sqrt (M i i) * Real.sqrt (M j j)) * diagonalNormalize M i j := by
  exact (mul_div_cancel₀ _ (mul_ne_zero (Real.sqrt_pos.2 (hd i)).ne'
    (Real.sqrt_pos.2 (hd j)).ne')).symm

/-- In a positive symmetric unit-diagonal matrix, a proportionality between
rows has coefficient one. This includes negative proportionalities in its
quantification and rules them out using the hypotheses. -/
theorem positive_unitDiagonal_proportional_eq_one (B : Matrix C C ℝ)
    (hpos : ∀ i j, 0 < B i j) (hsymm : ∀ i j, B i j = B j i)
    (hdiag : ∀ i, B i i = 1) (i j : C) (c : ℝ)
    (hrow : ∀ k, B i k = c * B j k) : c = 1 := by
  have hij : B i j = c := by simpa [hdiag] using hrow j
  have hprod : 1 = c * B i j := by simpa [hdiag, ← hsymm i j] using hrow i
  have hc : 0 < c := hij ▸ hpos i j
  rw [hij] at hprod
  nlinarith

/-- Distinct rows of a positive symmetric unit-diagonal matrix are
nonproportional over all real scalars. -/
theorem positive_unitDiagonal_rows_nonproportional (B : Matrix C C ℝ)
    (hpos : ∀ i j, 0 < B i j) (hsymm : ∀ i j, B i j = B j i)
    (hdiag : ∀ i, B i i = 1) (hrows : Function.Injective B)
    (i j : C) (hij : i ≠ j) (c : ℝ) : B i ≠ c • B j := by
  intro h
  have he : c = 1 := positive_unitDiagonal_proportional_eq_one B hpos hsymm hdiag i j c
    (fun k => congrFun h k)
  rw [he, one_smul] at h
  exact hij (hrows h)

/-- Equality of original rows is exactly equality of both normalized row
and diagonal amplitude. This identifies the original twin classes in §11.2. -/
theorem row_eq_iff_normalized_row_eq_and_diagonal_eq (M : Matrix C C ℝ)
    (hd : ∀ i, 0 < M i i) (hsymm : ∀ i j, M i j = M j i) (i j : C) :
    M i = M j ↔ diagonalNormalize M i = diagonalNormalize M j ∧ M i i = M j j := by
  constructor
  · intro h
    have hdiag : M i i = M j j := by
      calc
        M i i = M j i := congrFun h i
        _ = M i j := hsymm j i
        _ = M j j := congrFun h j
    refine ⟨?_, hdiag⟩
    funext k
    simp only [diagonalNormalize, congrFun h k, hdiag]
  · rintro ⟨hrow, hdiag⟩
    funext k
    have h := congrFun hrow k
    simp only [diagonalNormalize, hdiag] at h
    exact (div_left_inj' (mul_ne_zero (Real.sqrt_pos.2 (hd j)).ne'
      (Real.sqrt_pos.2 (hd k)).ne')).mp h

end PlanarHom
