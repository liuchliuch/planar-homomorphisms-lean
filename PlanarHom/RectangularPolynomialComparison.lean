import PlanarHom.RectangularWalshPolynomials
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots

/-! NEW polynomial comparison from the legal positive rational query interval.
The zero parameter is used only as a coefficient comparison after exact
polynomial equality has been proved. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Polynomial

theorem polynomial_eq_of_rational_interval (P Q:Polynomial ℝ)
    (h:∀t:ℚ,0<t→t<1→P.eval (t:ℝ)=Q.eval (t:ℝ)) : P=Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi:(Set.Ioo (0:ℚ) 1).Infinite:=Set.Ioo_infinite (by norm_num)
  have him:((fun t:ℚ=>(t:ℝ)) '' Set.Ioo (0:ℚ) 1).Infinite:=
    hi.image (Rat.cast_injective (α:=ℝ)).injOn
  apply him.mono
  rintro x ⟨t,ht,rfl⟩
  exact h t ht.1 ht.2

theorem coeff_mul_at_minimum (P Q:Polynomial ℝ) (n:ℕ)
    (hP:∀k,k<n→P.coeff k=0) : (P*Q).coeff n=P.coeff n*Q.coeff 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_single (n,0)
  · intro p hp hne
    have he:p.1+p.2=n:=Finset.mem_antidiagonal.mp hp
    have hlt:p.1<n:=by
      by_contra hh
      have hz:p.1=n ∧ p.2=0:=by omega
      exact hne (Prod.ext hz.1 hz.2)
    rw [hP p.1 hlt,zero_mul]
  · simp

theorem coeff_square_at_minimum (P:Polynomial ℝ) (n:ℕ)
    (hP:∀k,k<n→P.coeff k=0) : (P^2).coeff (2*n)=(P.coeff n)^2 := by
  rw [pow_two,coeff_mul]
  have hn:(n,n)∈Finset.antidiagonal (2*n):=by simp;omega
  rw [Finset.sum_eq_single (n,n)]
  · ring
  · intro p hp hne
    have he:p.1+p.2=2*n:=Finset.mem_antidiagonal.mp hp
    have hlt:p.1<n ∨ p.2<n:=by
      by_contra hh
      push_neg at hh
      have hz:p.1=n ∧ p.2=n:=by omega
      exact hne (Prod.ext hz.1 hz.2)
    rcases hlt with hlt|hlt
    · rw [hP p.1 hlt,zero_mul]
    · rw [hP p.2 hlt,mul_zero]
  · exact fun h=>False.elim (h hn)

theorem rowNormPolynomial_first_coeff {a b:ℕ} (C:Matrix (Boolean.Cube a) (Boolean.Cube b) ℝ)
    (S:Boolean.Cube a):
    (rowNormPolynomial C S).coeff (2*Boolean.degree S)=
      ∑T:Boolean.Cube b,((squareCoefficientPolynomial C S T).coeff (Boolean.degree S))^2:=by
  rw [rowNormPolynomial,finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro T _
  exact coeff_square_at_minimum _ _ (squarePolynomial_below_degree C S T)

end PlanarHom.RectangularWalshConvolution
