import PlanarHom.BinaryGcdBits

/-! # Exact canonical rational components under the signed-index encoding -/
namespace PlanarHom.BinaryArithmetic

/-- The integer codec stores `n` for nonnegative integers and the index `n` of
`Int.negSucc n` for negative integers. -/
def signedIndex (sign : Bool) (n : ℕ) : ℤ := if sign then Int.negSucc n else Int.ofNat n

def magnitudeIndex (sign : Bool) (n : ℕ) : ℕ := if sign then n+1 else n

@[simp] theorem signedIndex_natAbs (sign : Bool) (n : ℕ) :
    (signedIndex sign n).natAbs = magnitudeIndex sign n := by cases sign <;> rfl

def ratWord (sign : Bool) (num den : List Bool) : List Bool :=
  [true, true, true, sign, true, false] ++ Complexity.BitEncoding.frame num ++ den

/-- The exact nested framing of an integer/natural pair. -/
theorem encode_int_nat_pair (sign : Bool) (n d : ℕ) :
    (Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.nat).encode
      (signedIndex sign n, d) = ratWord sign (Computability.encodeNat n) (Computability.encodeNat d) := by
  cases sign <;> rfl

theorem normalization_gcd_pos (sign : Bool) (n d : ℕ) (hd : 0 < d) :
    0 < Nat.gcd (magnitudeIndex sign n) d := Nat.gcd_pos_of_pos_right _ hd

/-- The negative-constructor index is divided directly: `negSucc n / g` is
`negSucc (n/g)` for positive g. No predecessor conversion is required. -/
theorem mkRat_signedIndex_num (sign : Bool) (n d : ℕ) (hd : 0 < d) :
    (mkRat (signedIndex sign n) d).num =
      signedIndex sign (n / Nat.gcd (magnitudeIndex sign n) d) := by
  rw [Rat.num_mkRat]
  have hd0 : d ≠ 0 := by omega
  simp only [hd0, ↓reduceIte, signedIndex_natAbs, Nat.gcd_comm d]
  cases sign with
  | false => rfl
  | true =>
    have hg := normalization_gcd_pos true n d hd
    have hg' : (0 : ℤ) < (Nat.gcd (magnitudeIndex true n) d : ℕ) := Int.ofNat_lt.mpr hg
    simpa [signedIndex, Int.negSucc_eq] using Int.negSucc_ediv n hg'

theorem mkRat_signedIndex_den (sign : Bool) (n d : ℕ) (hd : 0 < d) :
    (mkRat (signedIndex sign n) d).den = d / Nat.gcd (magnitudeIndex sign n) d := by
  rw [Rat.den_mkRat]
  simp [hd.ne', Nat.gcd_comm, signedIndex_natAbs]

/-- Exact output word of canonical normalization for a nonzero denominator. -/
theorem encode_mkRat_signedIndex (sign : Bool) (n d : ℕ) (hd : 0 < d) :
    Complexity.BitEncoding.rat.encode (mkRat (signedIndex sign n) d) =
      ratWord sign
        (Computability.encodeNat (n / Nat.gcd (magnitudeIndex sign n) d))
        (Computability.encodeNat (d / Nat.gcd (magnitudeIndex sign n) d)) := by
  change (Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.nat).encode
    ((mkRat (signedIndex sign n) d).num, (mkRat (signedIndex sign n) d).den) = _
  rw [mkRat_signedIndex_num sign n d hd, mkRat_signedIndex_den sign n d hd]
  exact encode_int_nat_pair _ _ _

/-- A zero denominator has the unique canonical rational zero encoding. -/
@[simp] theorem encode_mkRat_zero_den (z : ℤ) :
    Complexity.BitEncoding.rat.encode (mkRat z 0) =
      [true, true, true, false, true, false, false, true] := by
  simp [Complexity.BitEncoding.rat, Complexity.BitEncoding.prod,
    Complexity.BitEncoding.int, Complexity.BitEncoding.retract,
    Complexity.BitEncoding.bool, Complexity.BitEncoding.nat,
    Complexity.BitEncoding.frame, Computability.encodeNat, Computability.encodeNum,
    Computability.encodePosNum]

end PlanarHom.BinaryArithmetic
