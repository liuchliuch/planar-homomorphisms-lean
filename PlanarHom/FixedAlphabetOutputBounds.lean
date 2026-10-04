import PlanarHom.EncodingSizeBounds
import PlanarHom.IntegerCoordinateBounds

/-!
# Polynomial encoded size of sums of fixed-alphabet words

The alphabet and rational basis are fixed. A common integer denominator gives
exponential coordinate representatives, and the verified rational normalization
machine turns those representatives into polynomial-length canonical codewords.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedAlphabetOutputBounds
open Complexity IntegerCoordinateBounds EncodingSizeBounds

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)
variable {ι : Type} [Fintype ι] {A : ι → K}

/-- An explicit polynomial for any chosen denominator certificate. -/
def outputPolynomial (data : ClearedCoordinates basis A) (Q : ℕ) : Polynomial ℕ :=
  (coordinateOutputPolynomial dimension (Q * growthConstant data) data.denominator).comp
    (Polynomial.X + Polynomial.C 1)

/-- At most exponentially many words of a common length have polynomial encoded sum size. -/
theorem sum_words_encoding_length_le (data : ClearedCoordinates basis A) (Q : ℕ)
    {J : Type} [Fintype J] (words : J → List ι) (L : ℕ)
    (hlen : ∀ j, (words j).length = L) (hcard : Fintype.card J ≤ Q ^ (L + 1)) :
    ((numberFieldEncoding basis).encode (∑ j, ((words j).map A).prod)).length ≤
      (outputPolynomial basis data Q).eval L := by
  have hcoord (i : Fin dimension) : ∃ z : ℤ, ∃ d : ℕ,
      basis.equivFun (∑ j, ((words j).map A).prod) i = mkRat z d ∧
      z.natAbs ≤ (Q * growthConstant data) ^ (L + 1) ∧
      d ≤ data.denominator ^ (L + 1) := by
    refine ⟨∑ j, numeratorWord data (words j) i, data.denominator ^ (L + 1), ?_, ?_, le_rfl⟩
    · rw [coordinates_sum_words basis data words L hlen, Rat.mkRat_eq_div, Nat.cast_pow]
    · calc
        (∑ j, numeratorWord data (words j) i).natAbs ≤
            Fintype.card J * growthConstant data ^ (L + 1) :=
          sum_words_numerator_bound basis data words L hlen i
        _ ≤ Q ^ (L + 1) * growthConstant data ^ (L + 1) := Nat.mul_le_mul_right _ hcard
        _ = (Q * growthConstant data) ^ (L + 1) := (mul_pow _ _ _).symm
  have hc := rational_coordinates_length_le (basis.equivFun (∑ j, ((words j).map A).prod)) hcoord
  simpa only [numberFieldEncoding, BitEncoding.retract, outputPolynomial,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using hc

/-- No coordinate certificate is an assumption: every fixed finite alphabet admits the bound. -/
theorem exists_output_polynomial (A : ι → K) (Q : ℕ) :
    ∃ p : Polynomial ℕ, ∀ {J : Type} [Fintype J] (words : J → List ι) (L : ℕ),
      (∀ j, (words j).length = L) → Fintype.card J ≤ Q ^ (L + 1) →
      ((numberFieldEncoding basis).encode (∑ j, ((words j).map A).prod)).length ≤ p.eval L := by
  obtain ⟨data⟩ := exists_clearedCoordinates basis A
  exact ⟨outputPolynomial basis data Q, fun words L hlen hcard =>
    sum_words_encoding_length_le basis data Q words L hlen hcard⟩

end PlanarHom.FixedAlphabetOutputBounds
