import PlanarHom.CubeCommutators
import PlanarHom.SymmetricBCHSector

/-!
# Rational BCH sectors force affine cube diagonals

This joins the genuine logarithmic cubic expansion to the exact cube
commutator calculation. Source-family availability and its sector-support
maximality proof remain separate hypotheses, not invented axioms.
-/

noncomputable section
namespace PlanarHom.Boolean
open scoped BigOperators Matrix.Norms.Operator

/-- Coordinate flip matrices are real symmetric. -/
theorem bitFlipMatrix_symm {d : ℕ} (r : Fin d) (z w : Cube d) :
    bitFlipMatrix r z w = bitFlipMatrix r w z := by
  have he : (w = flip z r) ↔ z = flip w r := eq_flip_iff z w r
  simp only [bitFlipMatrix, he]

/-- A scalar diagonal plus a real direction sum is Hermitian. -/
theorem scalar_add_directions_isHermitian {d : ℕ} (c : ℝ) (a : Fin d → ℝ) :
    (c • 1 + ∑ r, a r • bitFlipMatrix r).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro z w
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    star_trivial, bitFlipMatrix_symm _ w z]
  simp [Matrix.one_apply, eq_comm]

/-- Direction sums vanish off the diagonal and cube edges. -/
theorem scalar_add_directions_nonedge {d : ℕ} (c : ℝ) (a : Fin d → ℝ)
    (z w : Cube d) (hzw : z ≠ w) (hn : ∀ r, w ≠ flip z r) :
    (c • 1 + ∑ r, a r • bitFlipMatrix r) z w = 0 := by
  simp [Matrix.sum_apply, bitFlipMatrix, hzw, hn]

/-- Rational sector zeros of the actual log force the diagonal potential affine.
No mixed-difference identity or double-commutator zero is assumed. -/
theorem diagonal_affine_of_rational_log_sector {d : ℕ}
    (B : Matrix (Cube d) (Cube d) ℝ) (hsym : ∀ z w, B z w = B w z)
    (hopposite : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      B z (flip z r) = B (flip z s) (flip (flip z s) r))
    (hsupport : ∀ z w, z ≠ w → (∀ r, w ≠ flip z r) → B z w = 0)
    (c : ℝ) (a : Fin d → ℝ) (ha : ∀ r, a r ≠ 0)
    (hsector : ∀ z w, z ≠ w → (∀ r, w ≠ flip z r) →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℚ, 0 < (η : ℝ) → (η : ℝ) < η₀ →
        ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < ε →
          EntropyCompletion.matrixLog (SymmetricBCH.sandwich
            (c • 1 + ∑ r, a r • bitFlipMatrix r) ((η : ℝ) • B) (q : ℝ)) z w = 0)
    (z : Cube d) :
    B z z = B (fun _ => false) (fun _ => false) +
      ∑ r, (B (unitBit r) (unitBit r) - B (fun _ => false) (fun _ => false)) *
        (if z r then 1 else 0) := by
  have hB : B.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro z w
    simpa only [star_trivial] using hsym w z
  apply diagonal_affine_of_cube_commutator_obstruction B hsym hopposite hsupport c a ha _ z
  intro z w hzw hn
  obtain ⟨η₀, hη₀, hs⟩ := hsector z w hzw hn
  exact (SymmetricBCH.double_commutator_entry_zero_of_rational_sector
    (c • 1 + ∑ r, a r • bitFlipMatrix r) B (scalar_add_directions_isHermitian c a) hB z w
    (scalar_add_directions_nonedge c a z w hzw hn) (hsupport z w hzw hn) η₀ hη₀ hs).1

end PlanarHom.Boolean
