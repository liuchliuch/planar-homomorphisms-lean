import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Base-field Lagrange interpolation of algebra-valued polynomials. The target
algebra may have zero divisors; only the scalar node field is a field. -/
noncomputable section
open Classical
open scoped BigOperators Polynomial
namespace PlanarHom.AlgebraPolynomialInterpolation
variable {K R : Type} [Field K] [CommRing R] [Algebra K R] {D : ℕ}

theorem mapped_monomial (μ : Fin (D+1)→K) (hμ : Function.Injective μ) (r : ℕ) (hr : r≤D) :
    (Polynomial.X^r : Polynomial R)=
      ∑j,Polynomial.C (algebraMap K R (μ j^r))*(Lagrange.basis Finset.univ μ j).map (algebraMap K R) := by
  have hp : (Polynomial.X^r : Polynomial K).degree<(Finset.univ : Finset (Fin (D+1))).card := by
    simp only [Polynomial.degree_X_pow,Finset.card_univ,Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hr
  have h:=Lagrange.eq_interpolate (v:=μ) (s:=Finset.univ) hμ.injOn hp
  have hm:=congrArg (Polynomial.map (algebraMap K R)) h
  simpa [Lagrange.interpolate_apply,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.eval_pow] using hm

theorem interpolate (μ : Fin (D+1)→K) (hμ : Function.Injective μ)
    (P : Polynomial R) (hP : P.natDegree≤D) :
    P=∑j,Polynomial.C (P.eval (algebraMap K R (μ j)))*
      (Lagrange.basis Finset.univ μ j).map (algebraMap K R) := by
  calc
    P=∑r∈Finset.range (D+1),Polynomial.C (P.coeff r)*Polynomial.X^r :=
      P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hP)
    _=∑r∈Finset.range (D+1),∑j : Fin (D+1),
        Polynomial.C (P.coeff r)*Polynomial.C (algebraMap K R (μ j^r))*
          (Lagrange.basis Finset.univ μ j).map (algebraMap K R) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [mapped_monomial μ hμ r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)),Finset.mul_sum]
      simp only [mul_assoc]
    _=∑j : Fin (D+1),(∑r∈Finset.range (D+1),
        Polynomial.C (P.coeff r)*Polynomial.C (algebraMap K R (μ j^r)))*
          (Lagrange.basis Finset.univ μ j).map (algebraMap K R) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _=_ := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simp only [←Polynomial.C_mul,←map_sum]
      congr 1
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
      simp only [map_pow]

/-- The base-field polynomial is exactly the executable numerator coefficient
list scaled by the inverse product of all other node differences. -/
theorem basis_formula (μ : Fin (D+1)→K) (j : Fin (D+1)) :
    Lagrange.basis Finset.univ μ j=
      Polynomial.C ((∏k∈Finset.univ.erase j,(μ j-μ k))⁻¹)*
        ∏k∈Finset.univ.erase j,(Polynomial.X-Polynomial.C (μ k)) := by
  simp only [Lagrange.basis,Lagrange.basisDivisor,Finset.prod_mul_distrib]
  rw [←map_prod,←Finset.prod_inv_distrib]

/-- Coordinate reconstruction formula for the actual ascending coefficient lists. -/
theorem coefficient_interpolation (μ : Fin (D+1)→K) (hμ : Function.Injective μ)
    (P : Polynomial R) (hP : P.natDegree≤D) (r : ℕ) :
    P.coeff r=∑j,P.eval (algebraMap K R (μ j))*
      algebraMap K R ((Lagrange.basis Finset.univ μ j).coeff r) := by
  have h:=congrArg (fun Q : Polynomial R=>Q.coeff r) (interpolate μ hμ P hP)
  simpa only [Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_map] using h

/-- Ascending integer nodes0,...,D are distinct in the base field. -/
theorem integer_nodes_injective [CharZero K] :
    Function.Injective (fun j : Fin (D+1)=>(j.val : K)) := by
  intro i j h
  apply Fin.ext
  change (i.val : K)=(j.val : K) at h
  exact_mod_cast h

theorem integer_coefficient_interpolation [CharZero K] (P : Polynomial R)
    (hP : P.natDegree≤D) (r : ℕ) :
    P.coeff r=∑j : Fin (D+1),P.eval (algebraMap K R (j.val : K))*
      algebraMap K R ((Lagrange.basis Finset.univ (fun k : Fin (D+1)=>(k.val : K)) j).coeff r) :=
  coefficient_interpolation _ integer_nodes_injective P hP r

end PlanarHom.AlgebraPolynomialInterpolation
