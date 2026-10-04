import PlanarHom.CubeTensorExponential
import PlanarHom.CubeDirections
import PlanarHom.ExponentialDual

/-!
# Explicit two-by-two coordinate blocks

The affine diagonal plus direction-constant cube edges is exactly a scalar
identity plus coordinate lifts of the explicit blocks `[[0,b],[b,a]]`.
Exponentiating gives genuine positive-definite local factors.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.CubeTensorExponential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Away from its active coordinate, a lift preserves every bit. -/
theorem coordinateLift_apply_of_eq (r : ι) (A : Matrix Bool Bool ℝ) (z w : ι → Bool)
    (h : ∀ k, k ≠ r → z k = w k) : coordinateLift r A z w = A (z r) (w r) := by
  unfold coordinateLift
  have hp : (∏ k ∈ Finset.univ.erase r, (1 : Matrix Bool Bool ℝ) (z k) (w k)) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [h k (Finset.mem_erase.mp hk).1]
    simp
  rw [hp, mul_one]

/-- A coordinate lift vanishes if another coordinate changes. -/
theorem coordinateLift_apply_eq_zero (r : ι) (A : Matrix Bool Bool ℝ) (z w : ι → Bool)
    (h : ¬∀ k, k ≠ r → z k = w k) : coordinateLift r A z w = 0 := by
  push_neg at h
  obtain ⟨k, hkr, hkw⟩ := h
  unfold coordinateLift
  have hp : (∏ k ∈ Finset.univ.erase r, (1 : Matrix Bool Bool ℝ) (z k) (w k)) = 0 :=
    Finset.prod_eq_zero (by simp [hkr]) (Matrix.one_apply_ne hkw)
  rw [hp, mul_zero]

@[simp] theorem coordinateLift_diag (r : ι) (A : Matrix Bool Bool ℝ) (z : ι → Bool) :
    coordinateLift r A z z = A (z r) (z r) :=
  coordinateLift_apply_of_eq r A z z (by intros; rfl)

/-- The source's local symmetric block, ordered by `false,true`. -/
def localBlock (a b : ℝ) : Matrix Bool Bool ℝ :=
  fun x y => if x then (if y then a else b) else (if y then b else 0)

theorem localBlock_isHermitian (a b : ℝ) : (localBlock a b).IsHermitian := by
  ext x y
  cases x <;> cases y <;> simp [localBlock]

/-- Each explicit block exponentiates to a genuine positive-definite factor. -/
theorem exp_localBlock_posDef (a b : ℝ) : (NormedSpace.exp ℝ (localBlock a b)).PosDef :=
  ExponentialDual.exp_posDef (localBlock_isHermitian a b)

/-- A block lift is exactly one affine-diagonal contribution plus a bit-flip matrix. -/
theorem coordinateLift_localBlock {d : ℕ} (r : Fin d) (a b : ℝ) :
    coordinateLift r (localBlock a b) =
      Matrix.diagonal (fun z : Boolean.Cube d => if z r then a else 0) +
        b • Boolean.bitFlipMatrix r := by
  ext z w
  by_cases hzw : z = w
  · subst w
    rw [coordinateLift_diag]
    cases hz : z r <;> simp [localBlock, hz]
  · by_cases hw : w = Boolean.flip z r
    · subst w
      have hothers : ∀ k, k ≠ r → z k = Boolean.flip z r k := by
        intro k hk
        simp [Boolean.flip_apply_ne z r k hk]
      rw [coordinateLift_apply_of_eq r _ z _ hothers]
      cases hz : z r <;>
        simp [Matrix.diagonal, Boolean.bitFlipMatrix, localBlock,
          Boolean.flip_apply_same, hz, hzw]
    · have hothers : ¬∀ k, k ≠ r → z k = w k := by
        intro ho
        have hcoord : z r ≠ w r := by
          intro hr
          apply hzw
          funext k
          by_cases hk : k = r
          · subst k; exact hr
          · exact ho k hk
        have hneg : w r = !(z r) := by
          cases hz : z r <;> cases hwr : w r <;> simp_all
        apply hw
        funext k
        by_cases hk : k = r
        · subst k; simpa only [Boolean.flip_apply_same] using hneg
        · simpa only [Boolean.flip_apply_ne z r k hk] using (ho k hk).symm
      rw [coordinateLift_apply_eq_zero r _ z w hothers]
      simp [Matrix.diagonal, Boolean.bitFlipMatrix, hw, hzw]

/-- Summing local blocks recovers the affine diagonal and all direction weights. -/
theorem sum_coordinateLift_localBlock {d : ℕ} (a b : Fin d → ℝ) :
    (∑ r, coordinateLift r (localBlock (a r) (b r))) =
      Matrix.diagonal (fun z : Boolean.Cube d => ∑ r, if z r then a r else 0) +
        ∑ r, b r • Boolean.bitFlipMatrix r := by
  simp_rw [coordinateLift_localBlock]
  rw [Finset.sum_add_distrib]
  congr 1
  ext z w
  by_cases hzw : z = w
  · subst w; simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, hzw]

/-- The source's logarithmic cube matrix has the actual sum-of-local-blocks representation. -/
theorem matrix_eq_scalar_add_localBlocks {d : ℕ}
    (B : Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ) (c : ℝ) (a b : Fin d → ℝ)
    (hdiag : ∀ z, B z z = c + ∑ r, if z r then a r else 0)
    (hdir : ∀ z r, B z (Boolean.flip z r) = b r)
    (hsupport : ∀ z w, z ≠ w → (∀ r, w ≠ Boolean.flip z r) → B z w = 0) :
    B = c • 1 + ∑ r, coordinateLift r (localBlock (a r) (b r)) := by
  rw [Boolean.matrix_eq_diagonal_add_bitFlip_sum B b hdir hsupport,
    sum_coordinateLift_localBlock]
  ext z w
  by_cases hzw : z = w
  · subst w; simp [hdiag, Matrix.sum_apply]
  · simp [hzw, Matrix.sum_apply]

/-- Combining the proved local decomposition with the true exponential gives
the tensor factorization appearing in Proposition 4.8. -/
theorem exp_eq_tensor_localBlocks {d : ℕ}
    (B : Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ) (c : ℝ) (a b : Fin d → ℝ)
    (hdiag : ∀ z, B z z = c + ∑ r, if z r then a r else 0)
    (hdir : ∀ z r, B z (Boolean.flip z r) = b r)
    (hsupport : ∀ z w, z ≠ w → (∀ r, w ≠ Boolean.flip z r) → B z w = 0) :
    NormedSpace.exp ℝ B =
      Real.exp c • tensor (fun r => NormedSpace.exp ℝ (localBlock (a r) (b r))) := by
  rw [matrix_eq_scalar_add_localBlocks B c a b hdiag hdir hsupport,
    exp_scalar_add_sum_coordinateLift]

end PlanarHom.CubeTensorExponential
