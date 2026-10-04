import PlanarHom.RectangularTensorNormPolynomial

/-! NEW exact leading-coefficient calculus for the norm polynomial identity.
All lower coefficients are checked algebraically; no asymptotic coefficient
oracles are introduced. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Polynomial

theorem coeff_mul_below (P Q:Polynomial ℝ) (m n k:ℕ)
    (hP:∀i,i<m→P.coeff i=0) (hQ:∀j,j<n→Q.coeff j=0) (hk:k<m+n):
    (P*Q).coeff k=0:=by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have he:p.1+p.2=k:=Finset.mem_antidiagonal.mp hp
  have hlt:p.1<m ∨ p.2<n:=by omega
  rcases hlt with hi|hj
  · rw [hP p.1 hi,zero_mul]
  · rw [hQ p.2 hj,mul_zero]

theorem coeff_mul_first (P Q:Polynomial ℝ) (m n:ℕ)
    (hP:∀i,i<m→P.coeff i=0) (hQ:∀j,j<n→Q.coeff j=0):
    (P*Q).coeff (m+n)=P.coeff m*Q.coeff n:=by
  rw [coeff_mul]
  apply Finset.sum_eq_single (m,n)
  · intro p hp hne
    have he:p.1+p.2=m+n:=Finset.mem_antidiagonal.mp hp
    have hlt:p.1<m ∨ p.2<n:=by
      by_contra h
      push_neg at h
      have hz:p.1=m ∧ p.2=n:=by omega
      exact hne (Prod.ext hz.1 hz.2)
    rcases hlt with hi|hj
    · rw [hP p.1 hi,zero_mul]
    · rw [hQ p.2 hj,mul_zero]
  · simp

theorem prod_polynomial_first {I:Type} (s:Finset I) (P:I→Polynomial ℝ) (m:ℕ)
    (hP:∀i∈s,∀k,k<m→(P i).coeff k=0):
    (∀k,k<m*s.card→(∏i∈s,P i).coeff k=0) ∧
      (∏i∈s,P i).coeff (m*s.card)=∏i∈s,(P i).coeff m:=by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hs:=ih (fun j hj=>hP j (Finset.mem_insert_of_mem hj))
    have hpi:=hP i (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.mul_add,Nat.mul_one]
    constructor
    · intro k hk
      apply coeff_mul_below (P i) (∏j∈s,P j) m (m*s.card) k hpi hs.1
      omega
    · rw [Nat.add_comm (m*s.card) m,coeff_mul_first _ _ m (m*s.card) hpi hs.1,hs.2,Finset.prod_insert hi]

theorem rowNormPolynomial_below {a b:ℕ} (C:Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ)
    (S:Boolean.Cube a) (k:ℕ) (hk:k<2*Boolean.degree S):
    (rowNormPolynomial C S).coeff k=0:=by
  rw [rowNormPolynomial,finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro T _
  rw [pow_two]
  apply coeff_mul_below _ _ (Boolean.degree S) (Boolean.degree S) k
    (squarePolynomial_below_degree C S T) (squarePolynomial_below_degree C S T)
  omega

theorem rowNorm_tensor_leading {d:ℕ} (C:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ)
    (hforms:∀t:ℚ,0<t→t<1→∃δ:ℝ,∃ρ:Fin d→ℝ,(∀i,0<ρ i) ∧
      physicalGram C (t:ℝ)=δ • Boolean.tensor ρ)
    (hzero:(rowNormPolynomial C (fun _=>false)).coeff 0=1) (S:Boolean.Cube d):
    (rowNormPolynomial C S).coeff (2*Boolean.degree S)=
      ∏i∈bitSupport S,(rowNormPolynomial C (Boolean.unitBit i)).coeff 2:=by
  have he:=congrArg (fun P:Polynomial ℝ=>P.coeff (2*Boolean.degree S))
    (rowNorm_tensor_polynomial C hforms S)
  have hsingle:∀i∈bitSupport S,∀k,k<2→(rowNormPolynomial C (Boolean.unitBit i)).coeff k=0:=by
    intro i _ k hk
    apply rowNormPolynomial_below
    simpa only [degree_eq_support_card,support_unitBit,Finset.card_singleton,Nat.mul_one] using hk
  have hp:=prod_polynomial_first (bitSupport S) (fun i=>rowNormPolynomial C (Boolean.unitBit i)) 2 hsingle
  rw [←degree_eq_support_card] at hp
  dsimp only at he hp
  have hpow:((rowNormPolynomial C (fun _=>false))^(Boolean.degree S)).coeff 0=1:=by
    rw [coeff_zero_eq_eval_zero,eval_pow,←coeff_zero_eq_eval_zero,hzero,one_pow]
  rw [coeff_mul_at_minimum _ _ _ (rowNormPolynomial_below C S),hpow,mul_one] at he
  rw [mul_comm (rowNormPolynomial C (fun _=>false))] at he
  rw [coeff_mul_at_minimum _ _ _ hp.1,hzero,mul_one,hp.2] at he
  exact he

end PlanarHom.RectangularWalshConvolution
