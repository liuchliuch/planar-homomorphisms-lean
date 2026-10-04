import PlanarHom.DenseOuterVariableDescent
import PlanarHom.DensePolynomialEvaluationMachines

/-! NEW: actual coefficient descent through every fixed extraneous variable,
returning an ordinary rational value. The input fraction is not normalized. -/
noncomputable section
namespace PlanarHom.DenseRationalConstantExtraction
open DensePolynomial DenseCoefficientSelection Complexity

def constantMap (d : ℕ) : ℚ →+* RationalFunction d :=
  (algebraMap (Poly d) (RationalFunction d)).comp (qHom d)

theorem inclusion_constant (d : ℕ) (q : ℚ) :
    DenseOuterVariableDescent.inclusion d (constantMap d q) = constantMap (d+1) q := by
  simp only [constantMap, RingHom.comp_apply, DenseOuterVariableDescent.inclusion,
    IsFractionRing.lift_algebraMap, DenseOuterVariableDescent.polynomialBaseMap, qHom]
  rfl

def extract : (d : ℕ) → FractionCode d → ℚ
  | 0,a => a.1 / a.2
  | d+1,a => extract d (descendFraction d a)

theorem fp_extract (d : ℕ) : FP (fractionEncoding d) rationalCode (extract d) := by
  induction d with
  | zero => exact FixedFieldArithmetic.fp_division rationalBasis
  | succ d ih => exact (fp_descendFraction d).comp ih

theorem extract_value (d : ℕ) (a : FractionCode d) (ha : FractionValid d a)
    (q : ℚ) (hq : fractionValue d a = constantMap d q) : extract d a = q := by
  induction d with
  | zero =>
    apply (constantMap 0).injective
    simpa only [extract, constantMap, fractionValue, qHom, interpret, RingHom.comp_apply,
      RingHom.id_apply, map_div₀] using hq
  | succ d ih =>
    exact ih (descendFraction d a) (descendFraction_valid d a ha)
      (DenseOuterVariableDescent.descendFraction_value d a ha (constantMap d q)
        (by rwa [inclusion_constant]))

theorem rationalFunction_charZero (d : ℕ) : CharZero (RationalFunction d) :=
  (RingHom.charZero_iff (ϕ := constantMap d) (constantMap d).injective).mp inferInstance

end PlanarHom.DenseRationalConstantExtraction
