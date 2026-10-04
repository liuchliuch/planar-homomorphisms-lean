import PlanarHom.PottsCenteredPolynomial
import PlanarHom.OccurrenceMatchings
import Mathlib.Algebra.Polynomial.Roots

/-! NEW reconstruction: every coefficient of the normalized centered Potts
polynomial is the literal sum over occurrence subsets of that cardinality. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open MultiGraph Polynomial
variable {V E : Type} [Fintype V] [Fintype E]

def interaction (q : ℕ) (i j : Fin q) : ℚ := (if i=j then (q:ℚ) else 0)-1

def selectedValue (G : MultiGraph V E) (q : ℕ) (A : Finset E) : ℚ :=
  (q:ℚ)⁻¹^Fintype.card V*∑ σ : V → Fin q,∏ e∈A,interaction q (σ (G.src e)) (σ (G.dst e))

theorem interaction_symmetric (q : ℕ) (i j : Fin q) : interaction q i j=interaction q j i := by
  simp [interaction,eq_comm]

theorem interaction_rowSum (q : ℕ) (i : Fin q) : (∑ j : Fin q,interaction q i j)=0 := by
  simp [interaction,Finset.sum_sub_distrib]

theorem polynomial_eq_subsets (G : MultiGraph V E) (q : ℕ) :
    polynomial G q=∑ A : Finset E,C (selectedValue G q A)*X^A.card := by
  apply Polynomial.funext
  intro x
  rw [eval_polynomial]
  simp only [unweighted_eq,eval_finset_sum,eval_mul,eval_C,eval_pow,eval_X]
  simp_rw [add_comm (1:ℚ),Finset.prod_add_one]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [Finset.prod_mul_distrib,Finset.prod_const]
  rw [← Finset.mul_sum]
  dsimp [selectedValue,interaction]
  ring

theorem coefficient_eq_subsets (G : MultiGraph V E) (q d : ℕ) :
    (polynomial G q).coeff d=∑ A : Finset E,if A.card=d then selectedValue G q A else 0 := by
  rw [polynomial_eq_subsets,finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro A _
  simp [coeff_C_mul,coeff_X_pow,eq_comm]
end PlanarHom.PottsCentered
