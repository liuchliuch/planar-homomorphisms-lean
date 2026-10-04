import PlanarHom.Interpolation
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Exact coefficient-dot-query recovery for the list-based shifted Lagrange algorithm. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.LagrangeRecovery
open Polynomial Interpolation
variable {K : Type} [Field K] {n : ℕ}

/-- The polynomial numerator at one retained node. -/
def numerator (μ : Fin n → K) (j : Fin n) : Polynomial K :=
  ∏ k ∈ Finset.univ.erase j, (X - C (μ k))

/-- Shifted queries start at exponent one, accounting for the extra μj factor. -/
def denominator (μ : Fin n → K) (j : Fin n) : K :=
  μ j * ∏ k ∈ Finset.univ.erase j, (μ j - μ k)

/-- Coefficients of this actual polynomial are the recovery weights. -/
def recoveryPolynomial (μ : Fin n → K) (j : Fin n) : Polynomial K :=
  C (denominator μ j)⁻¹ * numerator μ j

theorem denominator_ne_zero (μ : Fin n → K) (hμ : Function.Injective μ)
    (hzero : ∀ i, μ i ≠ 0) (j : Fin n) : denominator μ j ≠ 0 := by
  apply mul_ne_zero (hzero j)
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1 (hμ h).symm)

theorem recoveryPolynomial_node (μ : Fin n → K) (hμ : Function.Injective μ)
    (hzero : ∀ i, μ i ≠ 0) (j i : Fin n) :
    μ i * (recoveryPolynomial μ j).eval (μ i) = if i = j then 1 else 0 := by
  classical
  simp only [recoveryPolynomial, numerator, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  by_cases h : i = j
  · subst i
    rw [if_pos rfl]
    have hp : (∏ k ∈ Finset.univ.erase j, (μ j - μ k)) ≠ 0 :=
      (mul_ne_zero_iff.mp (denominator_ne_zero μ hμ hzero j)).2
    dsimp [denominator]
    field_simp [hzero j]
  · rw [if_neg h]
    have hz : (∏ k ∈ Finset.univ.erase j, (μ i - μ k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩) (sub_self _)
    rw [hz, mul_zero, mul_zero]

theorem recoveryPolynomial_degree_lt (μ : Fin n → K) (j : Fin n) :
    (recoveryPolynomial μ j).natDegree < n := by
  apply (natDegree_C_mul_le _ _).trans_lt
  rw [numerator, natDegree_finset_prod_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]
  have hj := j.isLt
  omega

/-- Every low-degree polynomial acts on shifted power-sum queries by its node evaluations. -/
theorem coefficient_dot_queries (p : Polynomial K) (hp : p.natDegree < n)
    (μ a : Fin n → K) :
    (∑ h : Fin n, p.coeff h.val * queryValues μ a h) =
      ∑ j, a j * (μ j * p.eval (μ j)) := by
  simp only [queryValues, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_eq_sum_range' hp, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [pow_succ]
  ring

/-- Exact individual coefficient recovery used by the executable Lagrange procedure. -/
theorem recover_one (μ a : Fin n → K) (hμ : Function.Injective μ)
    (hzero : ∀ i, μ i ≠ 0) (j : Fin n) :
    (∑ h : Fin n, (recoveryPolynomial μ j).coeff h.val * queryValues μ a h) = a j := by
  rw [coefficient_dot_queries _ (recoveryPolynomial_degree_lt μ j)]
  simp_rw [recoveryPolynomial_node μ hμ hzero]
  simp

/-- Dot-product implementation equivalent to the source replacement sum. -/
def evaluateReplacement (μ target y : Fin n → K) : K :=
  ∑ j, target j * ∑ h : Fin n, (recoveryPolynomial μ j).coeff h.val * y h

theorem evaluateReplacement_queryValues (μ target a : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    evaluateReplacement μ target (queryValues μ a) = ∑ j, target j * a j := by
  simp only [evaluateReplacement, recover_one μ a hμ hzero]

/-- The implemented formula directly recovers grouped signed assignment contributions. -/
theorem evaluateReplacement_grouped_queries {A : Type*} [Fintype A]
    (classOf : A → Fin n) (rest : A → K) (μ target : Fin n → K)
    (hμ : Function.Injective μ) (hzero : ∀ i, μ i ≠ 0) :
    evaluateReplacement μ target
      (fun h => ∑ a, rest a * μ (classOf a) ^ (h.val + 1)) =
        ∑ a, target (classOf a) * rest a := by
  have hy : (fun h => ∑ a, rest a * μ (classOf a) ^ (h.val + 1)) =
      queryValues μ (classCoefficients classOf rest) := funext (grouped_queryValues classOf rest μ)
  rw [hy, evaluateReplacement_queryValues μ target _ hμ hzero, sum_classCoefficients]

end PlanarHom.LagrangeRecovery
