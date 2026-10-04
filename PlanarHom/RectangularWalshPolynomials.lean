import PlanarHom.RectangularWalshConvolution
import Mathlib.Algebra.Polynomial.BigOperators

/-! NEW actual polynomial coefficients of the parallel-square gadget. The
polynomials are constructed from the fixed original coefficient matrix, so
identities on positive rational samples can later be compared at zero without
querying a degenerate constraint. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean Polynomial
variable {a b d:ℕ}

def intersectBits (S T:Cube d):Cube d:=fun i=>S i && T i

theorem degree_xor_add (S T:Cube d):
    Boolean.degree S+Boolean.degree T=Boolean.degree (xor S T)+2*Boolean.degree (intersectBits S T):=by
  simp only [Boolean.degree,intersectBits,Boolean.xor,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hb (x y:Bool): (if x then 1 else 0)+(if y then 1 else 0)=
      (if Bool.xor x y then 1 else 0)+2*(if x && y then 1 else 0 : ℕ):=by
    cases x <;> cases y <;> decide
  exact hb (S i) (T i)

theorem degree_xor_le (S T:Cube d):Boolean.degree (xor S T)≤Boolean.degree S+Boolean.degree T:=by
  rw [degree_xor_add]
  omega

theorem degree_split_le (S I:Cube d):Boolean.degree S≤Boolean.degree I+Boolean.degree (xor S I):=by
  have h:=degree_xor_le I (xor S I)
  have he:xor I (xor S I)=S:=by funext i;simp [Boolean.xor,Bool.xor_comm,Bool.xor_left_comm]
  simpa only [he] using h

def squareCoefficientPolynomial (C:Matrix (Cube a) (Cube b) ℝ) (S:Cube a) (T:Cube b):Polynomial ℝ:=
  ∑p:DoubleIndex a b,Polynomial.C (C p.1 p.2*C (xor S p.1) (xor T p.2))*
    X^(Boolean.degree p.1+Boolean.degree (xor S p.1))

def rowNormPolynomial (C:Matrix (Cube a) (Cube b) ℝ) (S:Cube a):Polynomial ℝ:=
  ∑T:Cube b,(squareCoefficientPolynomial C S T)^2

theorem squarePolynomial_eval (C:Matrix (Cube a) (Cube b) ℝ) (S:Cube a) (T:Cube b) (t:ℝ):
    (squareCoefficientPolynomial C S T).eval t=
      coefficientConvolution (noisyCoefficients C t) (noisyCoefficients C t) S T:=by
  simp only [squareCoefficientPolynomial,eval_finset_sum,eval_mul,eval_C,eval_pow,eval_X,
    coefficientConvolution,noisyCoefficients,noiseDiagonal,Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [pow_add]
  ring

theorem squarePolynomial_actual (B:Matrix (Cube a) (Cube b) ℝ) (S:Cube a) (T:Cube b) (t:ℝ):
    (squareCoefficientPolynomial (sourceCoefficients B) S T).eval t=
      sourceCoefficients (fun x y=>(noiseMatrix (d:=a) t*B) x y*(noiseMatrix (d:=a) t*B) x y) S T:=by
  rw [squarePolynomial_eval,←squaredNoise_coefficients]
  congr 1
  funext x y
  simp only [squaredNoise,source_noise_matrix]

theorem rowNormPolynomial_eval (C:Matrix (Cube a) (Cube b) ℝ) (S:Cube a) (t:ℝ):
    (rowNormPolynomial C S).eval t=
      ∑T:Cube b,(coefficientConvolution (noisyCoefficients C t) (noisyCoefficients C t) S T)^2:=by
  simp only [rowNormPolynomial,eval_finset_sum,eval_pow,squarePolynomial_eval]

theorem squarePolynomial_coeff (C:Matrix (Cube a) (Cube b) ℝ) (S:Cube a) (T:Cube b) (n:ℕ):
    (squareCoefficientPolynomial C S T).coeff n=
      ∑p:DoubleIndex a b,if Boolean.degree p.1+Boolean.degree (xor S p.1)=n then
        C p.1 p.2*C (xor S p.1) (xor T p.2) else 0:=by
  simp only [squareCoefficientPolynomial,finset_sum_coeff,coeff_C_mul,coeff_X_pow]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp_all [eq_comm]

theorem squarePolynomial_below_degree (C:Matrix (Cube a) (Cube b) ℝ) (S:Cube a) (T:Cube b)
    (n:ℕ) (hn:n<Boolean.degree S): (squareCoefficientPolynomial C S T).coeff n=0:=by
  rw [squarePolynomial_coeff]
  apply Finset.sum_eq_zero
  intro p _
  have hle:=degree_split_le S p.1
  rw [if_neg (by omega)]

end PlanarHom.RectangularWalshConvolution
