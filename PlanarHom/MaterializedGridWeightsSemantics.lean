import PlanarHom.MaterializedGridWeightsMachines
import PlanarHom.AlgebraPolynomialInterpolation
import PlanarHom.LagrangeRecoveryListSemantics

/-! The literal scalar weight circuit computes coefficient functionals on an
algebra-valued polynomial. Only the scalar node field is a field; the target
algebra may have zero divisors and dependent radicals. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MaterializedGridWeightsMachines
variable {K R : Type} [Field K] [CommRing R] [Algebra K R] {D : ℕ}

theorem weight_ofFn (μ y : Fin (D+1) → K) (hμ : Function.Injective μ) (j : Fin (D+1)) :
    weight ((List.ofFn μ,List.ofFn y),μ j)=
      ∑r : Fin (D+1),(Lagrange.basis Finset.univ μ j).coeff r.val*y r := by
  simp only [weight,others]
  rw [LagrangeRecoveryListSemantics.filtered_coefficients μ hμ j,
    LagrangeRecoveryListSemantics.zipWith_ofFn,List.sum_ofFn,
    LagrangeRecoveryListSemantics.filtered_product μ hμ j]
  rw [AlgebraPolynomialInterpolation.basis_formula]
  simp only [Polynomial.coeff_C_mul,LagrangeRecovery.numerator,div_eq_mul_inv,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem coefficient_functional (μ y : Fin (D+1) → K) (hμ : Function.Injective μ)
    (P : Polynomial R) (hP : P.natDegree≤D) :
    (∑r : Fin (D+1),P.coeff r.val*algebraMap K R (y r))=
      ∑j : Fin (D+1),P.eval (algebraMap K R (μ j))*
        algebraMap K R (weight ((List.ofFn μ,List.ofFn y),μ j)) := by
  simp_rw [AlgebraPolynomialInterpolation.coefficient_interpolation μ hμ P hP,
    Finset.sum_mul,weight_ofFn μ y hμ,map_sum,map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem grid_eq_ofFn (d : ℕ) :
    grid (K:=K) d=List.ofFn (fun j : Fin (d+1)=>(j.val : K)) := by
  apply List.ext_getElem (by simp [grid])
  intro i hi hj
  simp only [grid,List.getElem_map,List.getElem_range,List.getElem_ofFn]

theorem integer_coefficient_functional [CharZero K] (y : Fin (D+1)→K)
    (P : Polynomial R) (hP : P.natDegree≤D) :
    (∑r : Fin (D+1),P.coeff r.val*algebraMap K R (y r))=
      ∑j : Fin (D+1),P.eval (algebraMap K R (j.val : K))*
        algebraMap K R (weight ((grid D,List.ofFn y),(j.val : K))) := by
  rw [grid_eq_ofFn]
  exact coefficient_functional _ y AlgebraPolynomialInterpolation.integer_nodes_injective P hP

end PlanarHom.MaterializedGridWeightsMachines
