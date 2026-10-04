import PlanarHom.RationalNormalizationBits

/-! # Signed-magnitude multiplication and the canonical rational code -/
namespace PlanarHom.BinaryArithmetic

def signMagnitude (sign : Bool) (n : ℕ) : ℤ := if sign then -(n:ℤ) else n

@[simp] theorem signedIndex_eq_signMagnitude (sign : Bool) (n : ℕ) :
    signedIndex sign n = signMagnitude sign (magnitudeIndex sign n) := by
  cases sign <;> simp [signedIndex,signMagnitude,magnitudeIndex,Int.negSucc_eq]

theorem signMagnitude_mul (sa sb : Bool) (a b : ℕ) :
    signMagnitude sa a * signMagnitude sb b = signMagnitude (xor sa sb) (a*b) := by
  cases sa <;> cases sb <;> simp [signMagnitude]

def productSign (sa sb : Bool) (n : ℕ) : Bool := if n=0 then false else xor sa sb

def productIndex (sa sb : Bool) (n : ℕ) : ℕ := if productSign sa sb n then n-1 else n

/-- Canonical signed-index conversion handles a zero product before retaining a
negative sign. -/
theorem productIndex_correct (sa sb : Bool) (n : ℕ) :
    signedIndex (productSign sa sb n) (productIndex sa sb n) = signMagnitude (xor sa sb) n := by
  by_cases hn : n=0
  · subst n
    cases sa <;> cases sb <;> simp [productSign,productIndex,signedIndex,signMagnitude]
  · have hp : 0<n := by omega
    cases h : xor sa sb <;> simp [productIndex,productSign,hn,h,signedIndex,signMagnitude,Int.negSucc_eq]
    omega

/-- Actual natural multiplication and a single truncated predecessor produce the
correct signed integer product under the existing constructor-index codec. -/
theorem signedIndex_product (sa sb : Bool) (a b : ℕ) :
    signedIndex (productSign sa sb (magnitudeIndex sa a * magnitudeIndex sb b))
      (productIndex sa sb (magnitudeIndex sa a * magnitudeIndex sb b)) =
        signedIndex sa a * signedIndex sb b := by
  rw [productIndex_correct, signedIndex_eq_signMagnitude, signedIndex_eq_signMagnitude,
    signMagnitude_mul]

/-- The canonical code of a rational is its signed numerator/denominator word. -/
theorem rat_encode_signedIndex (q : ℚ) (sign : Bool) (n : ℕ) (hn : q.num = signedIndex sign n) :
    Complexity.BitEncoding.rat.encode q =
      ratWord sign (Computability.encodeNat n) (Computability.encodeNat q.den) := by
  change (Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.nat).encode
    (q.num,q.den) = _
  rw [hn]
  exact encode_int_nat_pair _ _ _

end PlanarHom.BinaryArithmetic
