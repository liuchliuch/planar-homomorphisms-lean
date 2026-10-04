import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! Literal Boolean-choice expansion of all coefficients of a product of linear factors. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.PolynomialChoiceExpansion
open Polynomial
variable {K : Type} [CommRing K] {N : ℕ}

/-- Number of selected X terms in a Boolean expansion choice. -/
def choiceDegree (b : Fin N → Bool) : ℕ := ∑ i, if b i then 1 else 0

/-- The corresponding product of constant terms. -/
def choiceWeight (μ : Fin N → K) (b : Fin N → Bool) : K := ∏ i, if b i then 1 else -μ i

/-- Multiplying actual monomials adds degrees and multiplies coefficients. -/
theorem prod_monomial {I : Type*} (s : Finset I) (d : I → ℕ) (c : I → K) :
    (∏ i ∈ s, monomial (d i) (c i)) = monomial (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, monomial_mul_monomial]

/-- All coefficients are actual finite sums of signed products, without an interpolation premise. -/
theorem linear_product_coefficient (μ : Fin N → K) (k : ℕ) :
    (∏ i, (X - C (μ i))).coeff k =
      ∑ b : Fin N → Bool, if choiceDegree b = k then choiceWeight μ b else 0 := by
  classical
  have hfactor (i : Fin N) : X - C (μ i) =
      ∑ b : Bool, monomial (if b then 1 else 0) (if b then 1 else -μ i) := by
    simp [sub_eq_add_neg]
    rfl
  simp_rw [hfactor]
  rw [Fintype.prod_sum]
  simp_rw [prod_monomial]
  simp only [finset_sum_coeff, coeff_monomial, choiceDegree, choiceWeight]

end PlanarHom.PolynomialChoiceExpansion
