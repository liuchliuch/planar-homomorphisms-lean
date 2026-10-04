import PlanarHom.FieldCoordinateCertificates
import PlanarHom.EncodingSizeBounds

/-! Explicit height control for common-denominator field arithmetic certificates. -/

noncomputable section
open scoped BigOperators
open Matrix
namespace PlanarHom.FieldCoordinateCertificates
open IntegerCoordinateBounds IntegerLinearSystemBounds

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

namespace Certificate

/-- Bounds on actual integer coordinate representatives and their shared denominator. -/
def Bounded {x : K} (a : Certificate basis x) (N D : ℕ) : Prop :=
  a.denominator ≤ D ∧ ∀ i, (a.numerator i).natAbs ≤ N

theorem bounded_add {x y : K} (a : Certificate basis x) (b : Certificate basis y)
    {Nx Dx Ny Dy : ℕ} (ha : a.Bounded Nx Dx) (hb : b.Bounded Ny Dy) :
    (a.add b).Bounded (Nx * Dy + Ny * Dx) (Dx * Dy) := by
  refine ⟨Nat.mul_le_mul ha.1 hb.1, fun i => ?_⟩
  apply (Int.natAbs_add_le _ _).trans
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
    Nat.add_le_add (Nat.mul_le_mul (ha.2 i) hb.1) (Nat.mul_le_mul (hb.2 i) ha.1)

theorem bounded_neg {x : K} (a : Certificate basis x) {N D : ℕ} (ha : a.Bounded N D) :
    a.neg.Bounded N D := by
  refine ⟨ha.1, fun i => ?_⟩
  simpa only [neg, Int.natAbs_neg] using ha.2 i

end Certificate

/-- Every entry of the actual cleared multiplication matrix has a linear numerator bound. -/
theorem integerMultiplicationMatrix_bound
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) {N D : ℕ} (ha : a.Bounded N D) (i j : Fin dimension) :
    (integerMultiplicationMatrix basis data a i j).natAbs ≤ growthConstant data * N := by
  apply (natAbs_sum_le _ _).trans
  calc
    (∑ k, (a.numerator k * data.transition k i j).natAbs) ≤
        ∑ _k : Fin dimension, N * transitionBound data := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (ha.2 k) (transition_entry_le_bound basis data k i j)
    _ = dimension * transitionBound data * N := by simp; ring
    _ ≤ growthConstant data * N := Nat.mul_le_mul_right _ (dimension_mul_transitionBound_le_growth basis data)

namespace Certificate

/-- Multiplication increases height by a fixed structure-constant factor. -/
theorem bounded_mul (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x y : K} (a : Certificate basis x) (b : Certificate basis y)
    {Nx Dx Ny Dy : ℕ} (ha : a.Bounded Nx Dx) (hb : b.Bounded Ny Dy) :
    (a.mul data b).Bounded (dimension * growthConstant data * Nx * Ny)
      (data.denominator * Dx * Dy) := by
  refine ⟨Nat.mul_le_mul (Nat.mul_le_mul_left _ ha.1) hb.1, fun i => ?_⟩
  change (∑ j, integerMultiplicationMatrix basis data a i j * b.numerator j).natAbs ≤ _
  apply (natAbs_sum_le _ _).trans
  calc
    (∑ j, (integerMultiplicationMatrix basis data a i j * b.numerator j).natAbs) ≤
        ∑ _j : Fin dimension, (growthConstant data * Nx) * Ny := by
      apply Finset.sum_le_sum
      intro j _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (integerMultiplicationMatrix_bound data a ha i j) (hb.2 j)
    _ = _ := by simp; ring

/-- One fixed-degree polynomial bounds both inverse numerator and inverse denominator. -/
def inverseHeightBound (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    (N D : ℕ) : ℕ := dimension.factorial * (growthConstant data * (N + D)) ^ dimension

/-- Cramer's rule provides polynomial height bounds because field dimension is fixed. -/
theorem bounded_inv (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) (hx : x ≠ 0)
    {N D : ℕ} (ha : a.Bounded N D) :
    (a.inv data hx).Bounded (inverseHeightBound data N D) (inverseHeightBound data N D) := by
  let B := growthConstant data * (N + D)
  have hH (i j : Fin dimension) :
      (integerMultiplicationMatrix basis data a i j).natAbs ≤ B :=
    (integerMultiplicationMatrix_bound data a ha i j).trans
      (Nat.mul_le_mul_left _ (Nat.le_add_right N D))
  have hb (i : Fin dimension) : ((a.denominator : ℤ) * data.initial i).natAbs ≤ B := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    apply (Nat.mul_le_mul ha.1 (initial_le_growth basis data i)).trans
    dsimp [B]
    nlinarith
  refine ⟨det_natAbs_le _ B hH, fun i => ?_⟩
  change (Matrix.cramer (integerMultiplicationMatrix basis data a)
    (fun j => (a.denominator : ℤ) * data.initial j) i *
    (integerMultiplicationMatrix basis data a).det.sign).natAbs ≤ _
  rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero
    (integerMultiplicationMatrix_det_ne_zero basis data a hx), mul_one]
  exact cramer_natAbs_le _ _ B hH hb i

/-- Concrete representative heights imply polynomial actual canonical encoding length. -/
theorem encoding_length_le {x : K} (a : Certificate basis x) {C D n : ℕ}
    (ha : a.Bounded (C ^ n) (D ^ n)) :
    ((Complexity.numberFieldEncoding basis).encode x).length ≤
      (EncodingSizeBounds.coordinateOutputPolynomial dimension C D).eval n := by
  apply EncodingSizeBounds.rational_coordinates_length_le (basis.equivFun x)
  intro i
  refine ⟨a.numerator i, a.denominator, ?_, ha.2 i, ha.1⟩
  rw [Rat.mkRat_eq_div]
  apply (eq_div_iff (by exact_mod_cast a.denominator_pos.ne')).mpr
  simpa only [mul_comm] using a.spec i

end Certificate
end PlanarHom.FieldCoordinateCertificates
