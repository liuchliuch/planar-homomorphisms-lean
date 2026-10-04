import PlanarHom.CubeDirections

/-!
# Commutators of cube flips and diagonal potentials

These are identities of actual finite matrices, supporting the mixed-difference
extraction in Proposition 4.8.
-/

noncomputable section
namespace PlanarHom.Boolean
open scoped BigOperators

/-- The ordinary associative-algebra commutator. -/
def matrixComm {d : ℕ} (A B : Matrix (Cube d) (Cube d) ℝ) := A * B - B * A

/-- A flip-diagonal commutator measures the potential difference across that edge. -/
theorem comm_flip_diagonal_apply {d : ℕ} (r : Fin d) (φ : Cube d → ℝ) (z w : Cube d) :
    matrixComm (bitFlipMatrix r) (Matrix.diagonal φ) z w =
      if w = flip z r then φ w - φ z else 0 := by
  simp only [matrixComm, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, bitFlipMatrix]
  split_ifs <;> ring

/-- The double commutator for two coordinate directions is their mixed potential
difference, supported exactly at the vertex obtained by those two flips. -/
theorem double_comm_flip_diagonal_apply {d : ℕ} (r s : Fin d)
    (φ : Cube d → ℝ) (z w : Cube d) :
    matrixComm (bitFlipMatrix r) (matrixComm (bitFlipMatrix s) (Matrix.diagonal φ)) z w =
      if w = flip (flip z r) s then φ w + φ z - φ (flip z r) - φ (flip z s) else 0 := by
  change (bitFlipMatrix r * matrixComm (bitFlipMatrix s) (Matrix.diagonal φ)) z w -
    (matrixComm (bitFlipMatrix s) (Matrix.diagonal φ) * bitFlipMatrix r) z w = _
  rw [bitFlipMatrix_mul_apply, mul_bitFlipMatrix_apply, comm_flip_diagonal_apply,
    comm_flip_diagonal_apply]
  have hiff : (flip w r = flip z s) ↔ w = flip (flip z r) s := by
    constructor
    · intro h
      have hh := congrArg (fun a => flip a r) h
      simpa only [flip_flip, flips_commute z s r] using hh
    · intro h
      rw [h, flips_commute (flip z r) s r, flip_flip]
  by_cases he : w = flip (flip z r) s
  · have hh := hiff.mpr he
    rw [if_pos he, if_pos hh, if_pos he, hh]
    ring
  · rw [if_neg he, if_neg (fun h => he (hiff.mp h)), if_neg he]
    ring

/-- Two distinct flips can only be performed in the two possible orders. -/
theorem two_flips_eq_iff {d : ℕ} (z : Cube d) (r s a b : Fin d) (hrs : r ≠ s) :
    flip (flip z r) s = flip (flip z a) b ↔
      (a = r ∧ b = s) ∨ (a = s ∧ b = r) := by
  constructor
  · intro h
    by_cases har : a = r
    · subst a
      exact Or.inl ⟨rfl, ((flip_eq_flip_iff (flip z r) s b).mp h).symm⟩
    by_cases hbr : b = r
    · subst b
      rw [flips_commute z a r] at h
      exact Or.inr ⟨((flip_eq_flip_iff (flip z r) s a).mp h).symm, rfl⟩
    have hi := congrFun h r
    simp only [flip_apply_ne _ s r hrs, flip_apply_same,
      flip_apply_ne _ b r (Ne.symm hbr), flip_apply_ne _ a r (Ne.symm har)] at hi
    cases hz : z r <;> simp [hz] at hi
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact flips_commute z _ _

/-- Commutators distribute through finite direction sums. -/
theorem double_comm_sum_bitFlip {d : ℕ} (b : Fin d → ℝ) (D : Matrix (Cube d) (Cube d) ℝ) :
    matrixComm (∑ r, b r • bitFlipMatrix r) (matrixComm (∑ s, b s • bitFlipMatrix s) D) =
      ∑ r, ∑ s, (b r * b s) • matrixComm (bitFlipMatrix r) (matrixComm (bitFlipMatrix s) D) := by
  simp only [matrixComm, Finset.sum_mul, Finset.mul_sum, Matrix.mul_sub, Matrix.sub_mul,
    Finset.sum_sub_distrib, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul,
    Finset.smul_sum]

/-- Finite summation over two distinct marked points. -/
theorem sum_pair_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (v : ℝ) :
    (∑ k : α, if k = a ∨ k = b then v else 0) = v + v := by
  have he : (Finset.univ.filter (fun k : α => k = a ∨ k = b)) = {a, b} := by
    ext k
    simp
  rw [← Finset.sum_filter, he]
  simp [hab, two_mul]

/-- At opposite square vertices the full double commutator is exactly twice
the product of direction weights times the mixed second potential difference. -/
theorem double_comm_directions_diagonal_square {d : ℕ} (b : Fin d → ℝ)
    (φ : Cube d → ℝ) (z : Cube d) (r s : Fin d) (hrs : r ≠ s) :
    matrixComm (∑ a, b a • bitFlipMatrix a)
      (matrixComm (∑ a, b a • bitFlipMatrix a) (Matrix.diagonal φ))
        z (flip (flip z r) s) =
      2 * b r * b s *
        (φ z + φ (flip (flip z r) s) - φ (flip z r) - φ (flip z s)) := by
  rw [double_comm_sum_bitFlip]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, double_comm_flip_diagonal_apply]
  let v := b r * b s * (φ z + φ (flip (flip z r) s) - φ (flip z r) - φ (flip z s))
  have he (a c : Fin d) : b a * b c *
      (if flip (flip z r) s = flip (flip z a) c then
        φ (flip (flip z r) s) + φ z - φ (flip z a) - φ (flip z c) else 0) =
      if (a = r ∧ c = s) ∨ (a = s ∧ c = r) then v else 0 := by
    have hi := two_flips_eq_iff z r s a c hrs
    by_cases hp : (a = r ∧ c = s) ∨ (a = s ∧ c = r)
    · rw [if_pos (hi.mpr hp), if_pos hp]
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp [v] <;> ring
    · rw [if_neg (fun h => hp (hi.mp h)), if_neg hp, mul_zero]
  simp_rw [he]
  have hneq : (r, s) ≠ (s, r) := fun h => hrs (congrArg Prod.fst h)
  have hsum := sum_pair_indicator (r, s) (s, r) hneq v
  rw [Fintype.sum_prod_type] at hsum
  simp only [Prod.mk.injEq] at hsum
  rw [hsum]
  dsimp [v]
  ring

/-- Nonzero coordinate weights convert a zero double-commutator square entry
into the exact mixed-difference identity needed for affine cube potentials. -/
theorem mixed_difference_eq_zero_of_double_comm_zero {d : ℕ} (b : Fin d → ℝ)
    (φ : Cube d → ℝ) (hb : ∀ r, b r ≠ 0)
    (hzero : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      matrixComm (∑ a, b a • bitFlipMatrix a)
        (matrixComm (∑ a, b a • bitFlipMatrix a) (Matrix.diagonal φ))
          z (flip (flip z r) s) = 0)
    (z : Cube d) (r s : Fin d) (hrs : r ≠ s) :
    φ z + φ (flip (flip z r) s) - φ (flip z r) - φ (flip z s) = 0 := by
  have h := hzero z r s hrs
  rw [double_comm_directions_diagonal_square b φ z r s hrs] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) (hb r)) (hb s))

/-- The finite algebraic end of Proposition 4.8: the commutator obstruction
forces the diagonal potential to be affine in the Boolean coordinates. -/
theorem affine_of_double_comm_zero {d : ℕ} (b : Fin d → ℝ) (φ : Cube d → ℝ)
    (hb : ∀ r, b r ≠ 0)
    (hzero : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      matrixComm (∑ a, b a • bitFlipMatrix a)
        (matrixComm (∑ a, b a • bitFlipMatrix a) (Matrix.diagonal φ))
          z (flip (flip z r) s) = 0) (z : Cube d) :
    φ z = φ (fun _ => false) +
      ∑ r, (φ (unitBit r) - φ (fun _ => false)) * (if z r then 1 else 0) := by
  apply affine_of_mixedDifference_eq_zero φ _ z
  intro z r s hrs
  exact mixed_difference_eq_zero_of_double_comm_zero b φ hb hzero z r s hrs

/-- Any two weighted direction operators commute. -/
theorem direction_sums_commute {d : ℕ} (a b : Fin d → ℝ) :
    Commute (∑ r, a r • bitFlipMatrix r) (∑ s, b s • bitFlipMatrix s) :=
  Commute.sum_left Finset.univ _ _ (fun r _ =>
    Commute.sum_right Finset.univ _ _ (fun s _ =>
      ((bitFlipMatrix_commute r s).smul_left (a r)).smul_right (b s)))

theorem matrixComm_add_left {d : ℕ} (A B D : Matrix (Cube d) (Cube d) ℝ) :
    matrixComm (A + B) D = matrixComm A D + matrixComm B D := by
  simp only [matrixComm, add_mul, mul_add]
  abel

theorem matrixComm_add_right {d : ℕ} (A B D : Matrix (Cube d) (Cube d) ℝ) :
    matrixComm A (B + D) = matrixComm A B + matrixComm A D := by
  simp only [matrixComm, add_mul, mul_add]
  abel

@[simp] theorem matrixComm_smul_one_left {d : ℕ} (c : ℝ) (A : Matrix (Cube d) (Cube d) ℝ) :
    matrixComm (c • 1) A = 0 := by
  simp [matrixComm]

/-- Scalar identity terms and the directional part of B drop out of the double
commutator; only its diagonal potential remains. -/
theorem double_comm_directions_reduce_diagonal {d : ℕ} (c : ℝ) (a b : Fin d → ℝ)
    (φ : Cube d → ℝ) :
    matrixComm (c • 1 + ∑ r, a r • bitFlipMatrix r)
      (matrixComm (c • 1 + ∑ r, a r • bitFlipMatrix r)
        (Matrix.diagonal φ + ∑ r, b r • bitFlipMatrix r)) =
      matrixComm (∑ r, a r • bitFlipMatrix r)
        (matrixComm (∑ r, a r • bitFlipMatrix r) (Matrix.diagonal φ)) := by
  have hc : matrixComm (∑ r, a r • bitFlipMatrix r) (∑ r, b r • bitFlipMatrix r) = 0 :=
    sub_eq_zero.mpr (direction_sums_commute a b).eq
  simp only [matrixComm_add_left, matrixComm_add_right, matrixComm_smul_one_left,
    hc, zero_add, add_zero]

/-- Two distinct flips do not return to the original vertex. -/
theorem two_flips_ne_self {d : ℕ} (z : Cube d) (r s : Fin d) (hrs : r ≠ s) :
    flip (flip z r) s ≠ z := by
  intro h
  have hr := congrFun h r
  rw [flip_apply_ne _ s r hrs, flip_apply_same] at hr
  cases hz : z r <;> simp [hz] at hr

/-- An opposite square vertex is not a one-step cube neighbor. -/
theorem two_flips_ne_single {d : ℕ} (z : Cube d) (r s a : Fin d) (hrs : r ≠ s) :
    flip (flip z r) s ≠ flip z a := by
  intro h
  by_cases har : a = r
  · subst a
    have he := congrFun h s
    rw [flip_apply_same, flip_apply_ne _ r s (Ne.symm hrs)] at he
    cases hz : z s <;> simp [hz] at he
  · have he := congrFun h r
    rw [flip_apply_ne _ s r hrs, flip_apply_same, flip_apply_ne _ a r (Ne.symm har)] at he
    cases hz : z r <;> simp [hz] at he

/-- The full finite cube conclusion of the BCH obstruction: once B is supported
on cube edges with opposite-square equality, vanishing nonedge double commutators
forces its actual diagonal entries to be affine in the coordinates. -/
theorem diagonal_affine_of_cube_commutator_obstruction {d : ℕ}
    (B : Matrix (Cube d) (Cube d) ℝ) (hsym : ∀ z w, B z w = B w z)
    (hopposite : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      B z (flip z r) = B (flip z s) (flip (flip z s) r))
    (hsupport : ∀ z w, z ≠ w → (∀ r, w ≠ flip z r) → B z w = 0)
    (c : ℝ) (a : Fin d → ℝ) (ha : ∀ r, a r ≠ 0)
    (hcomm : ∀ z w, z ≠ w → (∀ r, w ≠ flip z r) →
      matrixComm (c • 1 + ∑ r, a r • bitFlipMatrix r)
        (matrixComm (c • 1 + ∑ r, a r • bitFlipMatrix r) B) z w = 0)
    (z : Cube d) :
    B z z = B (fun _ => false) (fun _ => false) +
      ∑ r, (B (unitBit r) (unitBit r) - B (fun _ => false) (fun _ => false)) *
        (if z r then 1 else 0) := by
  apply affine_of_double_comm_zero a (fun z => B z z) ha _ z
  intro z r s hrs
  have h := hcomm z (flip (flip z r) s) (Ne.symm (two_flips_ne_self z r s hrs))
    (fun a => two_flips_ne_single z r s a hrs)
  rw [matrix_eq_diagonal_add_directions B hsym hopposite hsupport,
    double_comm_directions_reduce_diagonal] at h
  exact h

end PlanarHom.Boolean
