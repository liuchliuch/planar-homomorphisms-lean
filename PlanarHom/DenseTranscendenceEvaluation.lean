import PlanarHom.DenseRationalFunctionPresentation
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Dense iterated polynomials are equivalent to the paper's fixed-variable
multivariate polynomial ring. Algebraic independence gives injective exact
real interpretation and hence sound equality testing, without real ordering. -/
noncomputable section
namespace PlanarHom.DensePolynomial

/-- Fixed reindexing between nested dense axes and multivariate exponents. -/
def mvEquiv : (n:ℕ)→MvPolynomial (Fin n) ℚ≃+*Poly n
  | 0 => MvPolynomial.isEmptyRingEquiv ℚ (Fin 0)
  | n+1 => (MvPolynomial.finSuccEquiv ℚ n).toRingEquiv.trans
      (Polynomial.mapEquiv (mvEquiv n))

def polynomialRealEval {n:ℕ} (x:Fin n→ℝ) : Poly n→+*ℝ :=
  (MvPolynomial.aeval x).toRingHom.comp (mvEquiv n).symm.toRingHom

theorem polynomialRealEval_injective {n:ℕ} (x:Fin n→ℝ) (hx:AlgebraicIndependent ℚ x) :
    Function.Injective (polynomialRealEval x) :=
  (algebraicIndependent_iff_injective_aeval.mp hx).comp (mvEquiv n).symm.injective

def fractionRealEval {n:ℕ} (x:Fin n→ℝ) (hx:AlgebraicIndependent ℚ x) : RationalFunction n→+*ℝ :=
  IsFractionRing.lift (polynomialRealEval_injective x hx)

theorem fractionRealEval_polynomial {n:ℕ} (x:Fin n→ℝ) (hx:AlgebraicIndependent ℚ x) (p:Poly n) :
    fractionRealEval x hx (algebraMap (Poly n) (RationalFunction n) p)=polynomialRealEval x p :=
  IsFractionRing.lift_algebraMap (polynomialRealEval_injective x hx) p

/-- Literal numerator/denominator interpretation at the fixed transcendence
basis, including any noncanonical but valid fraction code. -/
theorem fractionRealEval_value {n:ℕ} (x:Fin n→ℝ) (hx:AlgebraicIndependent ℚ x) (a:FractionCode n) :
    fractionRealEval x hx (fractionValue n a)=
      polynomialRealEval x (interpret n a.1)/polynomialRealEval x (interpret n a.2) := by
  rw [fractionValue,map_div₀,fractionRealEval_polynomial,fractionRealEval_polynomial]

/-- This exact decision uses algebraic independence rather than numerical
approximation, interval comparisons or an arbitrary-real sign oracle. -/
theorem fractionEq_real_iff {n:ℕ} (x:Fin n→ℝ) (hx:AlgebraicIndependent ℚ x)
    (a b:FractionCode n) (ha:FractionValid n a) (hb:FractionValid n b) :
    fractionEq n a b=true ↔ fractionRealEval x hx (fractionValue n a)=
      fractionRealEval x hx (fractionValue n b) := by
  rw [fractionEq_value_iff n a b ha hb]
  exact (fractionRealEval x hx).injective.eq_iff.symm

end PlanarHom.DensePolynomial
