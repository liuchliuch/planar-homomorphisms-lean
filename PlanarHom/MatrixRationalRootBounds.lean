import PlanarHom.PowerRootLiftMatrix
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Data.Finset.Max

/-! # Scaling rational matrix eigenvalues to bounded integers

A product of matrix-entry denominators clears the entire matrix. Every rational
eigenvalue of the resulting integer matrix is an integer by the monic integral
root theorem. An elementary maximum-coordinate estimate bounds its magnitude
by the sum of the absolute matrix entries. No root algorithm is used here.
-/

noncomputable section
namespace PlanarHom.MatrixRationalRootBounds
open scoped BigOperators
open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

def denominator (A : Matrix I I ℚ) : ℕ := ∏ ij : I×I, (A ij.1 ij.2).den

def integerMatrix (A : Matrix I I ℚ) : Matrix I I ℤ :=
  fun i j => (A i j).num * (denominator A / (A i j).den : ℕ)

def bound (A : Matrix I I ℚ) : ℕ :=
  (∑ ij : I×I, (integerMatrix A ij.1 ij.2).natAbs) + 1

def shifted (A : Matrix I I ℚ) : Matrix I I ℚ :=
  (integerMatrix A).map (Int.castRingHom ℚ) + (bound A : ℚ) • (1 : Matrix I I ℚ)

theorem denominator_pos (A : Matrix I I ℚ) : 0 < denominator A :=
  Finset.prod_pos (fun ij _ => (A ij.1 ij.2).pos)

theorem denominator_dvd (A : Matrix I I ℚ) (i j : I) : (A i j).den ∣ denominator A :=
  Finset.dvd_prod_of_mem (fun ij : I×I => (A ij.1 ij.2).den) (Finset.mem_univ (i,j))

theorem integerMatrix_cast (A : Matrix I I ℚ) :
    (integerMatrix A).map (Int.castRingHom ℚ) = (denominator A : ℚ) • A := by
  ext i j
  have hd : ((A i j).den : ℚ) ≠ 0 := by exact_mod_cast (A i j).den_ne_zero
  change ((integerMatrix A i j : ℤ) : ℚ) = (denominator A : ℚ) * A i j
  simp only [integerMatrix, Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_div (denominator_dvd A i j) hd, ← Rat.den_mul_eq_num (A i j)]
  field_simp

theorem eigenvector_of_charpoly_root (A : Matrix I I ℚ) (r : ℚ)
    (hr : A.charpoly.eval r = 0) : ∃ v : I → ℚ, v ≠ 0 ∧ A *ᵥ v = r • v := by
  rw [Matrix.eval_charpoly] at hr
  obtain ⟨v, hv, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hr
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec] at he
  have he' := sub_eq_zero.mp he
  rw [← he']
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem scaled_eigen (A : Matrix I I ℚ) (r : ℚ) (v : I → ℚ)
    (he : A *ᵥ v = r • v) :
    (integerMatrix A).map (Int.castRingHom ℚ) *ᵥ v = ((denominator A : ℚ)*r) • v := by
  rw [integerMatrix_cast, Matrix.smul_mulVec, he, smul_smul]

theorem rational_eigenvalue_integer (Z : Matrix I I ℤ) (r : ℚ) (v : I → ℚ)
    (hv : v ≠ 0) (he : Z.map (Int.castRingHom ℚ) *ᵥ v = r • v) :
    ∃ z : ℤ, r = (z : ℚ) := by
  have hr := PowerRootLiftMatrix.charpoly_eval_zero_of_eigen _ r v hv he
  rw [Matrix.charpoly_map] at hr
  have hz : Polynomial.aeval r Z.charpoly = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hr
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic (Matrix.charpoly_monic Z) hz
  exact ⟨z, hz⟩

def mass (A : Matrix I I ℚ) : ℚ := ∑ i, ∑ j, |A i j|

theorem eigenvalue_abs_le_mass (A : Matrix I I ℚ) (r : ℚ) (v : I → ℚ)
    (hv : v ≠ 0) (he : A *ᵥ v = r • v) : |r| ≤ mass A := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|)
    ⟨j, Finset.mem_univ j⟩
  have hi' (j : I) : |v j| ≤ |v i| := hi j (Finset.mem_univ j)
  have hpos : 0 < |v i| := (abs_pos.mpr hj).trans_le (hi' j)
  have he' : |r| * |v i| = |∑ j, A i j*v j| := by
    rw [← abs_mul]
    have h := congrArg abs (congrFun he i)
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply] using h.symm
  have hrow : (∑ j, |A i j|) ≤ mass A := by
    unfold mass
    exact Finset.single_le_sum (f := fun k : I => ∑ j : I, |A k j|)
      (fun k _ => Finset.sum_nonneg (fun j _ => abs_nonneg (A k j))) (Finset.mem_univ i)
  have hb : |r| * |v i| ≤ mass A * |v i| := calc
    _ = |∑ j, A i j*v j| := he'
    _ ≤ ∑ j, |A i j*v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |v j| := by simp [abs_mul]
    _ ≤ ∑ j, |A i j| * |v i| := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_left (hi' j) (abs_nonneg _))
    _ = (∑ j, |A i j|) * |v i| := (Finset.sum_mul _ _ _).symm
    _ ≤ mass A * |v i| := mul_le_mul_of_nonneg_right hrow (abs_nonneg _)
  exact (mul_le_mul_right hpos).mp hb

theorem mass_integerMatrix (A : Matrix I I ℚ) :
    mass ((integerMatrix A).map (Int.castRingHom ℚ)) + 1 = (bound A : ℚ) := by
  simp [mass, bound, Fintype.sum_prod_type]

theorem bound_pos (A : Matrix I I ℚ) : 0 < bound A := Nat.succ_pos _

theorem shifted_eigen (A : Matrix I I ℚ) (r : ℚ) (v : I → ℚ)
    (he : A *ᵥ v = r • v) :
    shifted A *ᵥ v = ((denominator A : ℚ)*r+(bound A : ℚ)) • v := by
  rw [shifted, Matrix.add_mulVec, scaled_eigen A r v he,
    Matrix.smul_mulVec, Matrix.one_mulVec, add_smul]

end PlanarHom.MatrixRationalRootBounds
