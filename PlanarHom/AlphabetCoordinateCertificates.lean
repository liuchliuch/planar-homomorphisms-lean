import PlanarHom.FieldExpressionHeights
import PlanarHom.FixedAlphabetOutputBounds

/-! Common-denominator certificates for sums of equal-length fixed-alphabet words. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.FieldCoordinateCertificates
open IntegerCoordinateBounds

variable {K ι : Type} [Field K] [Algebra ℚ K] [Fintype ι] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K} {A : ι → K}

namespace Certificate

/-- Transport only the exact represented field value, leaving all integer data unchanged. -/
def congr {x y : K} (h : x = y) (a : Certificate basis x) : Certificate basis y := h ▸ a

/-- Word products use the same integer recurrence and common denominator as the output bound. -/
def word (data : ClearedCoordinates basis A) (xs : List ι) :
    Certificate basis ((xs.map A).prod) where
  denominator := data.denominator ^ (xs.length + 1)
  denominator_pos := pow_pos data.denominator_pos _
  numerator := numeratorWord data xs
  spec := by
    intro i
    rw [coordinates_word basis data, Nat.cast_pow]
    have hD : (data.denominator : ℚ) ^ (xs.length + 1) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast data.denominator_pos.ne')
    exact mul_div_cancel₀ _ hD

theorem word_bounded (data : ClearedCoordinates basis A) (xs : List ι) :
    (word data xs).Bounded (growthConstant data ^ (xs.length + 1))
      (data.denominator ^ (xs.length + 1)) :=
  ⟨le_rfl, fun i => numeratorWord_bound basis data xs i⟩

/-- Equal-length words are added without multiplying their common denominator. -/
def sumWords (data : ClearedCoordinates basis A) {J : Type} [Fintype J]
    (words : J → List ι) (L : ℕ) (hlen : ∀ j, (words j).length = L) :
    Certificate basis (∑ j, ((words j).map A).prod) where
  denominator := data.denominator ^ (L + 1)
  denominator_pos := pow_pos data.denominator_pos _
  numerator := fun i => ∑ j, numeratorWord data (words j) i
  spec := by
    intro i
    rw [coordinates_sum_words basis data words L hlen, Nat.cast_pow]
    have hD : (data.denominator : ℚ) ^ (L + 1) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast data.denominator_pos.ne')
    exact mul_div_cancel₀ _ hD

theorem sumWords_bounded (data : ClearedCoordinates basis A) {J : Type} [Fintype J]
    (words : J → List ι) (L : ℕ) (hlen : ∀ j, (words j).length = L) :
    (sumWords data words L hlen).Bounded (Fintype.card J * growthConstant data ^ (L + 1))
      (data.denominator ^ (L + 1)) :=
  ⟨le_rfl, fun i => sum_words_numerator_bound basis data words L hlen i⟩

theorem sumWords_bounded_exponential (data : ClearedCoordinates basis A) {J : Type} [Fintype J]
    (words : J → List ι) (L Q : ℕ) (hlen : ∀ j, (words j).length = L)
    (hcard : Fintype.card J ≤ Q ^ (L + 1)) :
    (sumWords data words L hlen).Bounded ((Q * growthConstant data) ^ (L + 1))
      (data.denominator ^ (L + 1)) := by
  apply bounded_mono _ (sumWords_bounded data words L hlen) _ le_rfl
  calc
    Fintype.card J * growthConstant data ^ (L + 1) ≤
        Q ^ (L + 1) * growthConstant data ^ (L + 1) := Nat.mul_le_mul_right _ hcard
    _ = _ := (mul_pow _ _ _).symm

end Certificate
end PlanarHom.FieldCoordinateCertificates
