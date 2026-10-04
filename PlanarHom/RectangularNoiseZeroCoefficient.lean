import PlanarHom.RectangularBooleanSubsets
import PlanarHom.RectangularPolynomialLeadingTerms

/-! NEW zero coefficient of the actual noise/parallel-square polynomial.
This is an algebraic evaluation after the source has been normalized, not a
query to the oracle at a degenerate constraint. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean Polynomial
variable {d:ℕ}

def emptyCoefficient (d:ℕ):Matrix (Cube d) (Cube d) ℝ:=
  fun S T=>if S=(fun _=>false) then (if T=(fun _=>false) then 1 else 0) else 0

theorem noisyCoefficients_zero (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0):
    noisyCoefficients C 0=emptyCoefficient d:=by
  funext S T
  simp only [noisyCoefficients,noiseDiagonal,Matrix.diagonal_mul,emptyCoefficient]
  by_cases hs:S=(fun _=>false)
  · subst S
    simp only [Boolean.degree,Bool.false_eq_true,ite_false,Finset.sum_const_zero,pow_zero,one_mul,hrow,ite_true]
  · have hd:Boolean.degree S≠0:=fun h=>hs ((degree_zero_iff S).mp h)
    simp only [hs,if_false,zero_pow hd,zero_mul]

theorem emptyCoefficient_convolution:
    coefficientConvolution (emptyCoefficient d) (emptyCoefficient d)=emptyCoefficient d:=by
  funext S T
  simp [coefficientConvolution,Fintype.sum_prod_type,emptyCoefficient,xor_eq_zero_iff]

theorem rowNorm_zero_coefficient (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0):
    (rowNormPolynomial C (fun _=>false)).coeff 0=1:=by
  rw [coeff_zero_eq_eval_zero,rowNormPolynomial_eval,noisyCoefficients_zero C hrow,emptyCoefficient_convolution]
  simp [emptyCoefficient]

theorem rowNorm_first_tensor_product (C:Matrix (Cube d) (Cube d) ℝ)
    (hrow:∀T,C (fun _=>false) T=if T=(fun _=>false) then 1 else 0)
    (hforms:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃ρ:Fin d→ℝ,(∀i,0<ρ i) ∧
      physicalGram C (t:ℝ)=δ • Boolean.tensor ρ) (S:Cube d):
    (rowNormPolynomial C S).coeff (2*Boolean.degree S)=
      ∏i∈bitSupport S,(rowNormPolynomial C (Boolean.unitBit i)).coeff 2:=
  rowNorm_tensor_leading C hforms (rowNorm_zero_coefficient C hrow) S

end PlanarHom.RectangularWalshConvolution
