import PlanarHom.RectangularWalshGram
import PlanarHom.RectangularBooleanSubsets
import PlanarHom.RectangularPolynomialComparison

/-! NEW exact polynomial tensor identity for the physical parallel-square
Gram. It is derived from the actual legal rational samples, with no simulation
of the zero-parameter constraint. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean Polynomial
variable {d:ℕ}

def eigenRatio (ρ:Fin d→ℝ) (i:Fin d):ℝ:=(1-ρ i)/(1+ρ i)

theorem eigenvalue_support_product (ρ:Fin d→ℝ) (hρ:∀i,1+ρ i≠0) (S:Cube d):
    eigenvalue ρ S=eigenvalue ρ (fun _=>false)*∏i∈bitSupport S,eigenRatio ρ i:=by
  have he:∀i,(1+(if S i then -1 else 1)*ρ i)=
      (1+ρ i)*(if S i then eigenRatio ρ i else 1):=by
    intro i
    by_cases hi:S i=true
    · simp only [hi,ite_true,neg_one_mul,eigenRatio]
      field_simp [hρ i]
      ring
    · simp [hi]
  simp only [eigenvalue,he,Finset.prod_mul_distrib,Bool.false_eq_true,ite_false,one_mul]
  congr 1
  simp only [bitSupport,Finset.prod_ite,Finset.prod_const_one,mul_one]

theorem support_unitBit (i:Fin d):bitSupport (unitBit i)={i}:=by
  ext j
  simp [bitSupport,unitBit]

theorem eigenvalue_tensor_identity (ρ:Fin d→ℝ) (hρ:∀i,1+ρ i≠0) (δ:ℝ) (S:Cube d):
    (δ*eigenvalue ρ S)*(δ*eigenvalue ρ (fun _=>false))^(Boolean.degree S)=
      (δ*eigenvalue ρ (fun _=>false))*(∏i∈bitSupport S,δ*eigenvalue ρ (unitBit i)):=by
  have hs:=eigenvalue_support_product ρ hρ S
  have hu:∀i,eigenvalue ρ (unitBit i)=eigenvalue ρ (fun _=>false)*eigenRatio ρ i:=by
    intro i
    rw [eigenvalue_support_product ρ hρ,support_unitBit,Finset.prod_singleton]
  simp_rw [hu]
  rw [hs,degree_eq_support_card]
  simp only [←mul_assoc,Finset.prod_mul_distrib,Finset.prod_const]
  ring

theorem rowNorm_of_physical_tensor (C:Matrix (Cube d) (Cube d) ℝ) (t δ:ℝ) (ρ:Fin d→ℝ)
    (h:physicalGram C t=δ • Boolean.tensor ρ) (S:Cube d):
    (rowNormPolynomial C S).eval t=δ*eigenvalue ρ S:=by
  have he:=congrFun (congrFun (convolution_gram_of_tensor C t δ ρ h) S) S
  simpa only [rowNormPolynomial_eval,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.smul_apply,Matrix.diagonal_apply_eq,smul_eq_mul,pow_two] using he

/-- The extra constant factor keeps the formula valid even in degree zero. -/
theorem rowNorm_tensor_polynomial (C:Matrix (Cube d) (Cube d) ℝ)
    (hforms:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃ρ:Fin d→ℝ,(∀i,0<ρ i) ∧
      physicalGram C (t:ℝ)=δ • Boolean.tensor ρ) (S:Cube d):
    rowNormPolynomial C S*(rowNormPolynomial C (fun _=>false))^(Boolean.degree S)=
      rowNormPolynomial C (fun _=>false)*(∏i∈bitSupport S,rowNormPolynomial C (unitBit i)):=by
  apply polynomial_eq_of_rational_interval
  intro t ht ht1
  obtain ⟨δ,ρ,hρ,hform⟩:=hforms t ht ht1
  simp only [eval_mul,eval_pow,eval_prod]
  simp_rw [rowNorm_of_physical_tensor C (t:ℝ) δ ρ hform]
  exact eigenvalue_tensor_identity ρ (fun i=>ne_of_gt (by linarith [hρ i])) δ S

end PlanarHom.RectangularWalshConvolution
