import PlanarHom.SampleSeparation
import PlanarHom.ExponentVectors
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

/-!
# Polynomial product identities and bounded integer separation

The polynomial case of Lemma 3.10 is proved for actual polynomial entries.
The exponent sum is the number of entry factors. Zero polynomials and the
empty product are allowed. No zero-count or equality oracle is assumed.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.PolynomialProductZeros

variable {E : Type*} [Fintype E]

def product (F : E → Polynomial ℝ) (a : E → ℕ) : Polynomial ℝ :=
  ∏ e, F e ^ a e

@[simp] theorem eval_product (F : E → Polynomial ℝ) (a : E → ℕ) (t : ℝ) :
    (product F a).eval t = ∏ e, (F e).eval t ^ a e := by
  simp [product, Polynomial.eval_prod]

theorem degree_product_le (F : E → Polynomial ℝ) (a : E → ℕ) (d m : ℕ)
    (hF : ∀ e, (F e).natDegree ≤ d) (ha : ∑ e, a e = m) :
    (product F a).natDegree ≤ d * m := by
  calc
    (product F a).natDegree ≤ ∑ e, (F e ^ a e).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ e, a e * d := Finset.sum_le_sum fun e _ =>
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hF e))
    _ = d * m := by rw [← Finset.sum_mul, ha, Nat.mul_comm]

/-- Every finite set of roots of a nonzero polynomial is bounded by degree. -/
theorem polynomial_zero_card_le (p : Polynomial ℝ) (hp : p ≠ 0)
    (T : Finset ℝ) (hT : ∀ t ∈ T, p.eval t = 0) : T.card ≤ p.natDegree := by
  by_contra! h
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p T hT h)

/-- Source (3.5), case (P), including signed and zero polynomial entries. -/
theorem agreement_card_le (F : E → Polynomial ℝ) (a b : E → ℕ) (d m : ℕ)
    (hF : ∀ e, (F e).natDegree ≤ d) (ha : ∑ e, a e = m) (hb : ∑ e, b e = m)
    (hne : (fun t : ℝ => ∏ e, (F e).eval t ^ a e) ≠
      (fun t : ℝ => ∏ e, (F e).eval t ^ b e))
    (T : Finset ℝ)
    (hT : ∀ t ∈ T, (∏ e, (F e).eval t ^ a e) = ∏ e, (F e).eval t ^ b e) :
    T.card ≤ d * m := by
  have hp : product F a - product F b ≠ 0 := by
    intro h
    have h' := sub_eq_zero.mp h
    exact hne (funext fun t => by
      simpa only [eval_product] using congrArg (fun p : Polynomial ℝ => p.eval t) h')
  refine (polynomial_zero_card_le _ hp T ?_).trans ?_
  · intro t ht
    simp only [Polynomial.eval_sub, eval_product, sub_eq_zero]
    exact hT t ht
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (degree_product_le F a d m hF ha) (degree_product_le F b d m hF hb))

/-- Equality of products is determined by `d*m+1` consecutive integer samples,
exactly the polynomial specialization of source (3.6). -/
theorem product_identity_iff_consecutive (F : E → Polynomial ℝ)
    (a b : E → ℕ) (d m n₀ : ℕ) (hF : ∀ e, (F e).natDegree ≤ d)
    (ha : ∑ e, a e = m) (hb : ∑ e, b e = m) :
    (fun t : ℝ => ∏ e, (F e).eval t ^ a e) =
        (fun t : ℝ => ∏ e, (F e).eval t ^ b e) ↔
      ∀ j ≤ d * m, (∏ e, (F e).eval ((n₀ + j : ℕ) : ℝ) ^ a e) =
        ∏ e, (F e).eval ((n₀ + j : ℕ) : ℝ) ^ b e := by
  constructor
  · intro h j _
    exact congrFun h (n₀ + j : ℕ)
  · intro h
    by_contra hne
    let T := (Finset.range (d * m + 1)).image fun j => ((n₀ + j : ℕ) : ℝ)
    have hc : T.card = d * m + 1 := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro x y hxy
        exact Nat.add_left_cancel (Nat.cast_injective hxy)
    have hh := agreement_card_le F a b d m hF ha hb hne T (by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      exact h j (by have := Finset.mem_range.mp hj; omega))
    omega

/-- One polynomially bounded positive integer separates all product functions
of a fixed factor count. Repeated exponent vectors are harmless. -/
theorem exists_separating_integer {I : Type*} [Fintype I]
    (F : E → Polynomial ℝ) (a : I → E → ℕ) (d m n₀ : ℕ)
    (hF : ∀ e, (F e).natDegree ≤ d) (ha : ∀ i, ∑ e, a i e = m) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + Fintype.card I ^ 2 * (d * m) ∧
      ∀ i j, (∏ e, (F e).eval (n : ℝ) ^ a i e) =
        (∏ e, (F e).eval (n : ℝ) ^ a j e) ↔
        (fun t : ℝ => ∏ e, (F e).eval t ^ a i e) =
          (fun t : ℝ => ∏ e, (F e).eval t ^ a j e) := by
  apply SampleSeparation.exists_function_separating_nat_sample_of_injective
    (fun i t => ∏ e, (F e).eval t ^ a i e) (fun n => (n : ℝ))
    Nat.cast_injective n₀ (d * m)
  intro i j hne T hT
  exact agreement_card_le F (a i) (a j) d m hF (ha i) (ha j) hne T hT

end PlanarHom.PolynomialProductZeros
