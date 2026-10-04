import PlanarHom.CubeAffine
import Mathlib.Data.Matrix.Basic
import PlanarHom.CartesianGeometry

/-!
# Direction weights on the Boolean cube

Exact square identities force opposite positive edge weights to agree. Cube
flip invariance then propagates them to entire coordinate directions. These
finite algebraic steps support Proposition 4.8; availability and analytic
support preservation are separate obligations.
-/

noncomputable section
namespace PlanarHom.Boolean
open scoped BigOperators

/-- Flip one cube coordinate. -/
def flip {d : ℕ} (z : Cube d) (r : Fin d) : Cube d := xor z (unitBit r)

@[simp] theorem flip_apply_same {d : ℕ} (z : Cube d) (r : Fin d) : flip z r r = !z r := by
  simp [flip, xor, unitBit]

@[simp] theorem flip_apply_ne {d : ℕ} (z : Cube d) (r s : Fin d) (h : s ≠ r) :
    flip z r s = z s := by simp [flip, xor, unitBit, h]

@[simp] theorem flip_flip {d : ℕ} (z : Cube d) (r : Fin d) : flip (flip z r) r = z := by
  funext i
  by_cases hi : i = r
  · subst i; simp
  · simp [hi]

@[simp] theorem flip_zero {d : ℕ} (r : Fin d) : flip (fun _ => false) r = unitBit r := by
  funext i
  simp [flip, xor]

theorem flip_ne_self {d : ℕ} (z : Cube d) (r : Fin d) : flip z r ≠ z := by
  intro h
  have hr := congrFun h r
  simp only [flip_apply_same] at hr
  cases hzr : z r <;> simp [hzr] at hr

theorem flip_eq_flip_iff {d : ℕ} (z : Cube d) (r s : Fin d) : flip z r = flip z s ↔ r = s := by
  constructor
  · intro h
    by_contra hrs
    have hr := congrFun h r
    rw [flip_apply_same, flip_apply_ne z s r hrs] at hr
    cases hzr : z r <;> simp [hzr] at hr
  · rintro rfl; rfl

theorem flips_commute {d : ℕ} (z : Cube d) (r s : Fin d) : flip (flip z r) s = flip (flip z s) r := by
  funext i
  by_cases hir : i = r <;> by_cases his : i = s
  · subst r; subst s; rfl
  · subst r; simp [his]
  · subst s; simp [hir]
  · simp [hir, his]

/-- A function unchanged by every bit flip is constant on the whole cube. -/
theorem constant_of_flip_invariant {d : ℕ} (f : Cube d → ℝ)
    (h : ∀ z r, f (flip z r) = f z) (z : Cube d) : f z = f (fun _ => false) := by
  have hm : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      f z + f (xor (xor z (unitBit r)) (unitBit s)) -
        f (xor z (unitBit r)) - f (xor z (unitBit s)) = 0 := by
    intro z r s _
    change f z + f (flip (flip z r) s) - f (flip z r) - f (flip z s) = 0
    rw [h, h, h]
    ring
  have hu (r : Fin d) : f (unitBit r) = f (fun _ => false) := by simpa using h (fun _ => false) r
  have hf := affine_of_mixedDifference_eq_zero f hm z
  simpa only [hu, sub_self, zero_mul, Finset.sum_const_zero, add_zero] using hf

/-- The two positive diagonal-path product equations force opposite square
weights to agree, as used in Proposition 4.8. -/
theorem opposite_weights_eq_of_square_products {a b c e : ℝ}
    (ha : 0 < a) (_hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (h₁ : a * b = e * c) (h₂ : a * e = b * c) : a = c ∧ b = e := by
  have h₁' := congrArg (fun x : ℝ => x * e) h₁
  have h₂' := congrArg (fun x : ℝ => x * b) h₂
  have hs : c * e ^ 2 = c * b ^ 2 := by nlinarith [h₁', h₂']
  have hs' : e ^ 2 = b ^ 2 := mul_left_cancel₀ (ne_of_gt hc) hs
  have hbe : b = e := by nlinarith
  refine ⟨?_, hbe⟩
  rw [hbe] at h₁
  exact mul_right_cancel₀ (ne_of_gt he) (by simpa only [mul_comm] using h₁)

/-- Opposite-square equality propagates to all edges in one direction, with
symmetry supplying invariance under reversing that edge. -/
theorem direction_weight_constant {d : ℕ} (B : Matrix (Cube d) (Cube d) ℝ)
    (hsym : ∀ z w, B z w = B w z)
    (hopposite : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      B z (flip z r) = B (flip z s) (flip (flip z s) r)) (z : Cube d) (r : Fin d) :
    B z (flip z r) = B (fun _ => false) (unitBit r) := by
  have hf : ∀ z s, B (flip z s) (flip (flip z s) r) = B z (flip z r) := by
    intro z s
    by_cases hrs : r = s
    · subst s
      rw [flip_flip]
      exact hsym _ _
    · exact (hopposite z r s hrs).symm
  simpa only [flip_zero] using constant_of_flip_invariant (fun z => B z (flip z r)) hf z

/-- The actual matrix that flips one coordinate and preserves all others. -/
def bitFlipMatrix {d : ℕ} (r : Fin d) : Matrix (Cube d) (Cube d) ℝ :=
  fun z w => if w = flip z r then 1 else 0

@[simp] theorem bitFlipMatrix_self {d : ℕ} (r : Fin d) (z : Cube d) :
    bitFlipMatrix r z z = 0 := by simp [bitFlipMatrix, Ne.symm (flip_ne_self z r)]

@[simp] theorem bitFlipMatrix_flip {d : ℕ} (r s : Fin d) (z : Cube d) :
    bitFlipMatrix r z (flip z s) = if s = r then 1 else 0 := by
  simp only [bitFlipMatrix, flip_eq_flip_iff]

/-- A cube-supported matrix with constant direction weights is exactly its
diagonal plus the weighted sum of the genuine bit-flip matrices. -/
theorem matrix_eq_diagonal_add_bitFlip_sum {d : ℕ}
    (B : Matrix (Cube d) (Cube d) ℝ) (b : Fin d → ℝ)
    (hdir : ∀ z r, B z (flip z r) = b r)
    (hsupport : ∀ z w, z ≠ w → (∀ r, w ≠ flip z r) → B z w = 0) :
    B = Matrix.diagonal (fun z => B z z) + ∑ r, b r • bitFlipMatrix r := by
  ext z w
  by_cases hzw : z = w
  · subst w
    simp [Matrix.sum_apply]
  · by_cases hedge : ∃ r, w = flip z r
    · obtain ⟨r, rfl⟩ := hedge
      simp [hzw, Matrix.sum_apply, bitFlipMatrix_flip, hdir]
    · have hnone : ∀ r, w ≠ flip z r := not_exists.mp hedge
      rw [hsupport z w hzw hnone]
      simp [hzw, Matrix.sum_apply, bitFlipMatrix, hnone]

/-- Equation (4.6), derived from cube support and opposite-square equality. -/
theorem matrix_eq_diagonal_add_directions {d : ℕ}
    (B : Matrix (Cube d) (Cube d) ℝ) (hsym : ∀ z w, B z w = B w z)
    (hopposite : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      B z (flip z r) = B (flip z s) (flip (flip z s) r))
    (hsupport : ∀ z w, z ≠ w → (∀ r, w ≠ flip z r) → B z w = 0) :
    B = Matrix.diagonal (fun z => B z z) +
      ∑ r, B (fun _ => false) (unitBit r) • bitFlipMatrix r :=
  matrix_eq_diagonal_add_bitFlip_sum B _
    (fun z r => direction_weight_constant B hsym hopposite z r) hsupport

/-- Bit-flip adjacency is exactly the genuine Cartesian product of two-point cliques. -/
theorem hammingGraph_adj_iff_flip {d : ℕ} (z w : Cube d) :
    (CartesianGeometry.hammingGraph (fun _ : Fin d => Bool)).Adj z w ↔
      ∃ r, w = flip z r := by
  constructor
  · rintro ⟨r, hne, heq⟩
    refine ⟨r, ?_⟩
    funext i
    by_cases hir : i = r
    · subst i
      rw [flip_apply_same]
      cases hz : z r <;> cases hw : w r <;> simp_all
    · rw [flip_apply_ne z r i hir]
      exact (heq i hir).symm
  · rintro ⟨r, rfl⟩
    refine ⟨r, ?_, ?_⟩
    · simp only [flip_apply_same]
      cases hz : z r <;> simp
    · intro i hir
      exact (flip_apply_ne z r i hir).symm

/-- Involutive coordinate flips exchange the two sides of an equality. -/
theorem eq_flip_iff {d : ℕ} (z w : Cube d) (r : Fin d) :
    w = flip z r ↔ z = flip w r := by
  constructor <;> intro h
  · rw [h, flip_flip]
  · rw [h, flip_flip]

/-- Left multiplication by a flip matrix permutes the matrix rows. -/
theorem bitFlipMatrix_mul_apply {d : ℕ} (r : Fin d) (A : Matrix (Cube d) (Cube d) ℝ)
    (z w : Cube d) : (bitFlipMatrix r * A) z w = A (flip z r) w := by
  simp [Matrix.mul_apply, bitFlipMatrix]

/-- Right multiplication permutes the matrix columns. -/
theorem mul_bitFlipMatrix_apply {d : ℕ} (A : Matrix (Cube d) (Cube d) ℝ)
    (r : Fin d) (z w : Cube d) : (A * bitFlipMatrix r) z w = A z (flip w r) := by
  simp only [Matrix.mul_apply, bitFlipMatrix, mul_ite, mul_one, mul_zero]
  have he (k : Cube d) : (w = flip k r) ↔ k = flip w r := eq_flip_iff k w r
  simp_rw [he]
  simp

/-- Different coordinate flip matrices commute as actual matrix operators. -/
theorem bitFlipMatrix_commute {d : ℕ} (r s : Fin d) :
    Commute (bitFlipMatrix r) (bitFlipMatrix s) := by
  change bitFlipMatrix r * bitFlipMatrix s = bitFlipMatrix s * bitFlipMatrix r
  ext z w
  simp only [bitFlipMatrix_mul_apply, bitFlipMatrix, flips_commute z r s]

/-- Flipping the same coordinate twice is the identity operator. -/
@[simp] theorem bitFlipMatrix_mul_self {d : ℕ} (r : Fin d) :
    bitFlipMatrix r * bitFlipMatrix r = 1 := by
  ext z w
  simp [bitFlipMatrix_mul_apply, bitFlipMatrix, Matrix.one_apply, eq_comm]

end PlanarHom.Boolean
