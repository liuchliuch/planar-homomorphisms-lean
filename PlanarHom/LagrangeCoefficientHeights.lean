import PlanarHom.PolynomialChoiceExpansion
import PlanarHom.FixedAlphabetOutputBounds

/-!
# Polynomial encoded heights of Lagrange numerator coefficients

Each coefficient is expanded into Boolean choices over one fixed alphabet that
also contains zero, one and minus one. Every summand is padded to a common word
length. This retains a single controlled denominator even when the expansion
has exponentially many terms; no enumeration of that expansion is asserted.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.LagrangeCoefficientHeights
open Polynomial PolynomialChoiceExpansion Complexity FixedAlphabetOutputBounds

variable {K ι : Type} [Field K] [Algebra ℚ K] [Fintype ι]

abbrev ExtendedAlphabet (ι : Type) := Unit ⊕ (Bool ⊕ ι)

def extendedValue (A : ι → K) : ExtendedAlphabet ι → K
  | .inl _ => 0
  | .inr (.inl false) => 1
  | .inr (.inl true) => -1
  | .inr (.inr a) => A a

/-- Each factor contributes a word of the same length, even when its X term is chosen. -/
def choiceBlock (m : ℕ) (word : List ι) (b : Bool) : List (ExtendedAlphabet ι) :=
  if b then List.replicate (m + 1) (.inr (.inl false))
  else .inr (.inl true) :: word.map (fun a => .inr (.inr a))

omit [Fintype ι] in
theorem choiceBlock_length (m : ℕ) (word : List ι) (hword : word.length = m) (b : Bool) :
    (choiceBlock m word b).length = m + 1 := by
  cases b <;> simp [choiceBlock, hword]

omit [Algebra ℚ K] [Fintype ι] in
theorem choiceBlock_product (A : ι → K) (m : ℕ) (word : List ι) (b : Bool) :
    ((choiceBlock m word b).map (extendedValue A)).prod =
      if b then 1 else -(word.map A).prod := by
  cases b <;> simp [choiceBlock, extendedValue, List.map_map, Function.comp_def]

/-- A leading zero discards choices of the wrong degree without changing word length. -/
def coefficientWord {N : ℕ} (m : ℕ) (words : Fin N → List ι) (k : ℕ) (b : Fin N → Bool) :
    List (ExtendedAlphabet ι) :=
  (if choiceDegree b = k then .inr (.inl false) else .inl ()) ::
    (List.ofFn (fun i => choiceBlock m (words i) (b i))).flatten

omit [Fintype ι] in
theorem coefficientWord_length {N : ℕ} (m : ℕ) (words : Fin N → List ι)
    (hlen : ∀ i, (words i).length = m) (k : ℕ) (b : Fin N → Bool) :
    (coefficientWord m words k b).length = N * (m + 1) + 1 := by
  simp only [coefficientWord, List.length_cons, List.length_flatten,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  have hb : ∀ i, (choiceBlock m (words i) (b i)).length = m + 1 :=
    fun i => choiceBlock_length m (words i) (hlen i) (b i)
  simp_rw [hb]
  simp

omit [Algebra ℚ K] [Fintype ι] in
theorem coefficientWord_product {N : ℕ} (A : ι → K) (m : ℕ) (words : Fin N → List ι)
    (k : ℕ) (b : Fin N → Bool) :
    ((coefficientWord m words k b).map (extendedValue A)).prod =
      if choiceDegree b = k then choiceWeight (fun i => ((words i).map A).prod) b else 0 := by
  simp only [coefficientWord, List.map_cons, List.prod_cons, List.map_flatten,
    List.prod_flatten, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  simp_rw [choiceBlock_product]
  split <;> simp_all [extendedValue, choiceWeight]

omit [Algebra ℚ K] [Fintype ι] in
/-- Exact coefficients are represented as sums of uniformly padded fixed-alphabet words. -/
theorem coefficient_eq_sum_words {N : ℕ} (A : ι → K) (m : ℕ) (words : Fin N → List ι) (k : ℕ) :
    (∏ i, (X - C (((words i).map A).prod))).coeff k =
      ∑ b : Fin N → Bool, ((coefficientWord m words k b).map (extendedValue A)).prod := by
  simp only [linear_product_coefficient, coefficientWord_product]

/-- Every coefficient of every partial Lagrange numerator has polynomial bit length
in the product of the factor count and source-word length. -/
theorem exists_polynomial_coefficient_length_bound {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (A : ι → K) :
    ∃ p : Polynomial ℕ, ∀ (N m : ℕ) (words : Fin N → List ι),
      (∀ i, (words i).length = m) → ∀ k : ℕ,
      ((numberFieldEncoding basis).encode
        ((∏ i, (X - C (((words i).map A).prod))).coeff k)).length ≤
          p.eval (N * (m + 1) + 1) := by
  obtain ⟨p, hp⟩ := exists_output_polynomial basis (extendedValue A) 2
  refine ⟨p, fun N m words hlen k => ?_⟩
  rw [coefficient_eq_sum_words A m]
  apply hp (coefficientWord m words k) (N * (m + 1) + 1)
    (coefficientWord_length m words hlen k)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  apply Nat.pow_le_pow_right (by omega)
  nlinarith

end PlanarHom.LagrangeCoefficientHeights
