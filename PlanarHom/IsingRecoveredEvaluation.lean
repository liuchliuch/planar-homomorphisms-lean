import PlanarHom.IsingRationalSampleSemantics

/-! NEW evaluation of the recovered rational coefficients at an arbitrary
fixed represented parameter. Sampling uses positive rationals only, so the
final identity also includes zero, negative, and -1 parameters. -/
namespace PlanarHom.IsingRationalInterpolation
open Complexity PlanarityLRRealization
variable {K:Type} [CommRing K]

def evaluateCoefficients (f:ℚ→+*K) (ρ:K) (cs:List ℚ) : K :=
  CoefficientListAlgebra.evaluate ρ (cs.map f)

theorem polynomial_map (f:ℚ→+*K) (cs:List ℚ) :
    CoefficientListAlgebra.polynomial (cs.map f)=
      (CoefficientListAlgebra.polynomial cs).map f := by
  induction cs with
  | nil=>simp [CoefficientListAlgebra.polynomial]
  | cons c cs ih=>simp [CoefficientListAlgebra.polynomial,ih]

theorem evaluateCoefficients_eq (f:ℚ→+*K) (ρ:K) (cs:List ℚ) :
    evaluateCoefficients f ρ cs=(CoefficientListAlgebra.polynomial cs).eval₂ f ρ := by
  rw [evaluateCoefficients,CoefficientListAlgebra.evaluate_eq,polynomial_map,Polynomial.eval_map]

noncomputable section
variable (g:MixedCode) {bt ut:ℕ}

theorem planarCoefficients_value (hp:g.PlanarValid bt ut) (f:ℚ→+*K) (ρ:K) :
    evaluateCoefficients f ρ (planarCoefficients g)=
      (g.toMultiGraph hp.1).partition (BooleanTensorEasyAssembly.isingMatrix ρ) (fun _=>1) := by
  rw [evaluateCoefficients_eq,planar_polynomial g hp]
  exact (g.toMultiGraph hp.1).isingPartitionPolynomial_eval₂ f ρ

theorem surfaceCoefficients_value (ambient:ℕ) (hg:g.Valid bt ut) (rows:PlanarityRowFaceCode.Rows)
    (R:RotationRows (g.toMultiGraph hg)) (hr:PlanarityRowFaceCode.Realizes g hg rows R)
    (hbound:Module.finrank (ZMod 2) R.Homology≤2*ambient) (f:ℚ→+*K) (ρ:K) :
    evaluateCoefficients f ρ (surfaceCoefficients ambient g rows)=
      (g.toMultiGraph hg).partition (BooleanTensorEasyAssembly.isingMatrix ρ) (fun _=>1) := by
  rw [evaluateCoefficients_eq,surface_polynomial g ambient hg rows R hr hbound]
  exact (g.toMultiGraph hg).isingPartitionPolynomial_eval₂ f ρ

end
end PlanarHom.IsingRationalInterpolation
