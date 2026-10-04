import PlanarHom.FieldCoordinateCertificates

/-! Exact fixed-basis coordinate formulas used by the actual arithmetic circuits. -/
namespace PlanarHom.FixedFieldArithmetic
open Matrix IntegerCoordinateBounds FieldCoordinateCertificates
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

theorem multiplication_det_ne_zero (x : K) (hx : x≠0) :
    (multiplicationMatrix basis x).det ≠ 0 := by
  have hinj : Function.Injective (multiplicationMatrix basis x).mulVec := by
    intro u v huv
    have hu : u = basis.equivFun (basis.equivFun.symm u) := (basis.equivFun.apply_symm_apply u).symm
    have hv : v = basis.equivFun (basis.equivFun.symm v) := (basis.equivFun.apply_symm_apply v).symm
    rw [hu,hv,multiplicationMatrix_mulVec,multiplicationMatrix_mulVec] at huv
    exact basis.equivFun.symm.injective (mul_right_cancel₀ hx (basis.equivFun.injective huv))
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero

/-- Cramer fractions compute inverse coordinates even at zero, because division
by zero in the rational field returns zero. The field basis has positive size. -/
theorem inverse_coordinate (x : K) (i : Fin dimension) :
    basis.equivFun x⁻¹ i =
      Matrix.cramer (multiplicationMatrix basis x) (basis.equivFun 1) i /
        (multiplicationMatrix basis x).det := by
  classical
  by_cases hx : x=0
  · subst x
    letI : Nonempty (Fin dimension) := basis.index_nonempty
    have hz : multiplicationMatrix basis (0:K) = 0 := by
      simp [multiplicationMatrix]
    simp [hz]
  · have hd := multiplication_det_ne_zero basis x hx
    have hs : multiplicationMatrix basis x *ᵥ basis.equivFun x⁻¹ = basis.equivFun 1 := by
      rw [multiplicationMatrix_mulVec,inv_mul_cancel₀ hx]
    have heq : (multiplicationMatrix basis x).det • basis.equivFun x⁻¹ =
        Matrix.cramer (multiplicationMatrix basis x) (basis.equivFun 1) := by
      rw [Matrix.cramer_eq_adjugate_mulVec,←hs,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
        Matrix.smul_mulVec,Matrix.one_mulVec]
    apply (eq_div_iff hd).mpr
    simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using congrFun heq i

end PlanarHom.FixedFieldArithmetic
