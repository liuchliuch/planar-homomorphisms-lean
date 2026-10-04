import PlanarHom.IntegerLinearSystemBounds

/-!
# Common-denominator coordinate certificates

These are concrete integer representatives, not assumed arithmetic or complexity
operations. Their constructions supply the coefficient-height layer for exact
fixed-number-field interpolation.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace PlanarHom.FieldCoordinateCertificates
open IntegerCoordinateBounds IntegerLinearSystemBounds

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- A positive common denominator and exact integer coordinates. -/
structure Certificate (x : K) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  numerator : Fin dimension → ℤ
  spec : ∀ i, (denominator : ℚ) * basis.equivFun x i = numerator i

/-- Every field element has such a certificate in the fixed rational basis. -/
theorem exists_certificate (x : K) : Nonempty (Certificate basis x) := by
  obtain ⟨D, hD, z, hz⟩ := exists_common_denominator (basis.equivFun x)
  exact ⟨⟨D, hD, z, hz⟩⟩

namespace Certificate
variable {basis}

/-- Addition clears the two explicitly given denominators. -/
def add {x y : K} (a : Certificate basis x) (b : Certificate basis y) : Certificate basis (x + y) where
  denominator := a.denominator * b.denominator
  denominator_pos := Nat.mul_pos a.denominator_pos b.denominator_pos
  numerator := fun i => a.numerator i * b.denominator + b.numerator i * a.denominator
  spec := by
    intro i
    rw [map_add, Pi.add_apply, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_mul,
      Int.cast_natCast, Int.cast_natCast, ← a.spec i, ← b.spec i]
    ring

/-- Negation preserves the denominator and every coordinate magnitude. -/
def neg {x : K} (a : Certificate basis x) : Certificate basis (-x) where
  denominator := a.denominator
  denominator_pos := a.denominator_pos
  numerator := fun i => -a.numerator i
  spec := by intro i; simp only [map_neg, Pi.neg_apply, Int.cast_neg, ← a.spec i]; ring

end Certificate

/-- Multiplication by an arbitrary element is linear in its basis coordinates. -/
theorem multiplicationMatrix_expansion (x : K) (i j : Fin dimension) :
    multiplicationMatrix basis x i j =
      ∑ k, basis.equivFun x k * multiplicationMatrix basis (basis k) i j := by
  simp only [multiplicationMatrix, LinearMap.toMatrix_apply, LinearMap.mulRight_apply]
  conv_lhs => rw [← basis.sum_equivFun x]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Module.Basis.equivFun_apply]

/-- An integer matrix representing multiplication after one common clearing. -/
def integerMultiplicationMatrix (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) : Matrix (Fin dimension) (Fin dimension) ℤ :=
  fun i j => ∑ k, a.numerator k * data.transition k i j

/-- The integer matrix has exactly the intended rational multiplication action. -/
theorem integerMultiplicationMatrix_cast
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) :
    (fun i j => (integerMultiplicationMatrix basis data a i j : ℚ)) =
      ((data.denominator * a.denominator : ℕ) : ℚ) • multiplicationMatrix basis x := by
  ext i j
  simp only [integerMultiplicationMatrix, Int.cast_sum, Int.cast_mul, Matrix.smul_apply, smul_eq_mul,
    Nat.cast_mul]
  rw [multiplicationMatrix_expansion basis x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← a.spec k, ← data.transition_spec k i j]
  ring

/-- The cleared multiplication matrix is nonsingular whenever the field element is nonzero. -/
theorem integerMultiplicationMatrix_det_ne_zero
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) (hx : x ≠ 0) :
    (integerMultiplicationMatrix basis data a).det ≠ 0 := by
  let H := integerMultiplicationMatrix basis data a
  let Hq : Matrix (Fin dimension) (Fin dimension) ℚ := fun i j => H i j
  have hc : Hq = ((data.denominator * a.denominator : ℕ) : ℚ) • multiplicationMatrix basis x :=
    integerMultiplicationMatrix_cast basis data a
  have hs : ((data.denominator * a.denominator : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos data.denominator_pos a.denominator_pos).ne'
  have hinj : Function.Injective Hq.mulVec := by
    intro u v huv
    rw [hc, Matrix.smul_mulVec, Matrix.smul_mulVec] at huv
    have hm := (smul_right_injective _ hs) huv
    have hu : u = basis.equivFun (basis.equivFun.symm u) := (basis.equivFun.apply_symm_apply u).symm
    have hv : v = basis.equivFun (basis.equivFun.symm v) := (basis.equivFun.apply_symm_apply v).symm
    rw [hu, hv, multiplicationMatrix_mulVec, multiplicationMatrix_mulVec] at hm
    have he := mul_right_cancel₀ hx (basis.equivFun.injective hm)
    exact basis.equivFun.symm.injective he
  have hdq : Hq.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det Hq).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero
  intro hz
  apply hdq
  change ((Int.castRingHom ℚ).mapMatrix H).det = 0
  rw [← RingHom.map_det, hz, map_zero]

/-- Coordinates of the actual field inverse solve this integer system exactly. -/
theorem inverse_coordinate_system
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) (hx : x ≠ 0) :
    (fun i j => (integerMultiplicationMatrix basis data a i j : ℚ)) *ᵥ basis.equivFun x⁻¹ =
      fun i => (((a.denominator : ℤ) * data.initial i : ℤ) : ℚ) := by
  rw [integerMultiplicationMatrix_cast, Matrix.smul_mulVec, multiplicationMatrix_mulVec,
    inv_mul_cancel₀ hx]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  rw [← data.initial_spec i]
  ring

namespace Certificate
variable {basis}

/-- Actual field multiplication represented by an integer matrix-vector product. -/
def mul (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x y : K} (a : Certificate basis x) (b : Certificate basis y) : Certificate basis (x * y) where
  denominator := data.denominator * a.denominator * b.denominator
  denominator_pos := Nat.mul_pos (Nat.mul_pos data.denominator_pos a.denominator_pos) b.denominator_pos
  numerator := integerMultiplicationMatrix basis data a *ᵥ b.numerator
  spec := by
    intro i
    have hv : (fun j => (integerMultiplicationMatrix basis data a i j : ℚ)) ⬝ᵥ
        basis.equivFun y = ((data.denominator * a.denominator : ℕ) : ℚ) *
          basis.equivFun (x * y) i := by
      have h := congrFun (congrArg (fun H : Matrix (Fin dimension) (Fin dimension) ℚ =>
        H *ᵥ basis.equivFun y) (integerMultiplicationMatrix_cast basis data a)) i
      simpa only [Matrix.smul_mulVec, multiplicationMatrix_mulVec, Pi.smul_apply,
        smul_eq_mul, mul_comm y x] using h
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
    simp_rw [← b.spec]
    rw [show (∑ j, (integerMultiplicationMatrix basis data a i j : ℚ) *
        ((b.denominator : ℚ) * basis.equivFun y j)) =
        (b.denominator : ℚ) * ((fun j => (integerMultiplicationMatrix basis data a i j : ℚ)) ⬝ᵥ
          basis.equivFun y) by
      simp only [dotProduct, Finset.mul_sum]; congr 1; ext j; ring]
    rw [hv]
    push_cast
    ring

/-- Inversion is represented by Cramer's rule on the actual multiplication matrix. -/
def inv (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {x : K} (a : Certificate basis x) (hx : x ≠ 0) : Certificate basis x⁻¹ where
  denominator := (integerMultiplicationMatrix basis data a).det.natAbs
  denominator_pos := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr
    (integerMultiplicationMatrix_det_ne_zero basis data a hx))
  numerator := fun i => Matrix.cramer (integerMultiplicationMatrix basis data a)
    (fun j => (a.denominator : ℤ) * data.initial j) i *
      (integerMultiplicationMatrix basis data a).det.sign
  spec := by
    intro i
    have hd := integerMultiplicationMatrix_det_ne_zero basis data a hx
    have h := solution_eq_cramer (integerMultiplicationMatrix basis data a)
      (fun j => (a.denominator : ℤ) * data.initial j) (basis.equivFun x⁻¹) hd
      (inverse_coordinate_system basis data a hx) i
    rw [h, div_eq_mkRat_sign _ _ hd, Rat.mkRat_eq_div]
    have hn : (((integerMultiplicationMatrix basis data a).det.natAbs : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Int.natAbs_ne_zero.mpr hd)
    exact mul_div_cancel₀ _ hn

end Certificate

end PlanarHom.FieldCoordinateCertificates
