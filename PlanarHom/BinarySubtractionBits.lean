import PlanarHom.BinaryMultiplicationBits

/-! # Binary borrow arithmetic, comparison, and canonical subtraction -/
namespace PlanarHom.BinaryArithmetic

/-- Low difference bit of a full subtractor. -/
def fullSubtractBit (x y borrow : Bool) : Bool := xor (xor x y) borrow

/-- Borrow propagates exactly when the subtrahend plus incoming borrow exceeds
this position's minuend bit. -/
def fullSubtractBorrow (x y borrow : Bool) : Bool :=
  ((!x) && (y || borrow)) || (y && borrow)

/-- Subtract padded little-endian words. The output word has exactly the longer
input length; a separate final borrow records underflow. -/
def subtractWithBorrow (borrow : Bool) (xs ys : List Bool) : Bool × List Bool :=
  match xs, ys with
  | [], [] => (borrow, [])
  | x :: xs, [] =>
    let r := subtractWithBorrow (fullSubtractBorrow x false borrow) xs []
    (r.1, fullSubtractBit x false borrow :: r.2)
  | [], y :: ys =>
    let r := subtractWithBorrow (fullSubtractBorrow false y borrow) [] ys
    (r.1, fullSubtractBit false y borrow :: r.2)
  | x :: xs, y :: ys =>
    let r := subtractWithBorrow (fullSubtractBorrow x y borrow) xs ys
    (r.1, fullSubtractBit x y borrow :: r.2)
termination_by xs.length + ys.length

/-- Prepend a low bit without introducing a redundant encoding of zero. -/
def canonicalCons (b : Bool) (xs : List Bool) : List Bool :=
  if xs = [] then if b then [true] else [] else b :: xs

/-- Remove high zeroes, preserving all significant bits. -/
def normalizeBits : List Bool → List Bool
  | [] => []
  | b :: bs => canonicalCons b (normalizeBits bs)

@[simp] theorem canonicalCons_true (xs : List Bool) : canonicalCons true xs = true :: xs := by
  cases xs <;> simp [canonicalCons]

@[simp] theorem canonicalCons_false (xs : List Bool) : canonicalCons false xs = shiftBits xs := by
  simp [canonicalCons, shiftBits]

@[simp] theorem canonicalCons_encodeNat (b : Bool) (n : ℕ) :
    canonicalCons b (Computability.encodeNat n) =
      Computability.encodeNat ((if b then 1 else 0) + 2*n) := by
  cases b with
  | false => simp
  | true =>
    have h := succBits_encodeNat (2*n)
    rw [← shiftBits_encodeNat] at h
    have hs : succBits (shiftBits (Computability.encodeNat n)) =
        true :: Computability.encodeNat n := by
      generalize Computability.encodeNat n = xs
      cases xs <;> simp [shiftBits, succBits]
    rw [hs] at h
    simpa [Nat.add_comm] using h

/-- Normalization produces precisely the canonical code of the represented
natural, even for arbitrary padded input words. -/
theorem normalizeBits_eq_encode (xs : List Bool) :
    normalizeBits xs = Computability.encodeNat (bitValue xs) := by
  induction xs with
  | nil => simp [normalizeBits, bitValue, Computability.encodeNat, Computability.encodeNum]
  | cons b xs ih => simp [normalizeBits, bitValue, ih]

@[simp] theorem normalizeBits_append_false (xs : List Bool) :
    normalizeBits (xs ++ [false]) = normalizeBits xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.cons_append, normalizeBits, ih]

@[simp] theorem normalizeBits_append_true (xs : List Bool) :
    normalizeBits (xs ++ [true]) = xs ++ [true] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [normalizeBits, ih, canonicalCons]

/-- The machine sees the difference most-significant-bit first and discards
leading zeroes before its final reversal. -/
def trimFalse : List Bool → List Bool
  | false :: bs => trimFalse bs
  | bs => bs

@[simp] theorem trimFalse_reverse (xs : List Bool) :
    (trimFalse xs).reverse = normalizeBits xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [trimFalse, List.reverse_cons, ih]

theorem bitValue_lt_pow_length (xs : List Bool) : bitValue xs < 2^xs.length := by
  induction xs with
  | nil => simp [bitValue]
  | cons b xs ih =>
    cases b <;> simp only [bitValue, Bool.false_eq_true, ↓reduceIte, List.length_cons,
      pow_succ] <;> omega

theorem subtractWithBorrow_length (c : Bool) (xs ys : List Bool) :
    (subtractWithBorrow c xs ys).2.length = max xs.length ys.length := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subtractWithBorrow]
    | cons y ys ih => simp [subtractWithBorrow, ih]
  | cons x xs ih =>
    cases ys with
    | nil => simp [subtractWithBorrow, ih]
    | cons y ys => simp [subtractWithBorrow, ih]

/-- The fixed-width difference and final borrow exactly express integer
subtraction, not an abstract arithmetic operation of the machine. -/
theorem subtractWithBorrow_value (c : Bool) (xs ys : List Bool) :
    (bitValue (subtractWithBorrow c xs ys).2 : ℤ) -
      (if (subtractWithBorrow c xs ys).1 then (2 : ℤ)^((subtractWithBorrow c xs ys).2.length)
        else 0) =
      (bitValue xs : ℤ) - bitValue ys - (if c then 1 else 0) := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [subtractWithBorrow, bitValue]
    | cons y ys ih =>
      have h := ih (fullSubtractBorrow false y c)
      rw [subtractWithBorrow]
      clear ih
      generalize subtractWithBorrow (fullSubtractBorrow false y c) [] ys = r at h ⊢
      rcases r with ⟨d, bs⟩
      cases y <;> cases c <;> cases d <;>
        simp_all [fullSubtractBit, fullSubtractBorrow, bitValue,
          pow_succ, Nat.cast_add, Nat.cast_mul]
      all_goals omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := ih (fullSubtractBorrow x false c) []
      rw [subtractWithBorrow]
      clear ih
      generalize subtractWithBorrow (fullSubtractBorrow x false c) xs [] = r at h ⊢
      rcases r with ⟨d, bs⟩
      cases x <;> cases c <;> cases d <;>
        simp_all [fullSubtractBit, fullSubtractBorrow, bitValue,
          pow_succ, Nat.cast_add, Nat.cast_mul]
      all_goals omega
    | cons y ys =>
      have h := ih (fullSubtractBorrow x y c) ys
      rw [subtractWithBorrow]
      clear ih
      generalize subtractWithBorrow (fullSubtractBorrow x y c) xs ys = r at h ⊢
      rcases r with ⟨d, bs⟩
      cases x <;> cases y <;> cases c <;> cases d <;>
        simp_all [fullSubtractBit, fullSubtractBorrow, bitValue,
          pow_succ, Nat.cast_add, Nat.cast_mul]
      all_goals omega


/-- Underflow is equivalent to the expected strict comparison. -/
theorem subtractWithBorrow_borrow (c : Bool) (xs ys : List Bool) :
    (subtractWithBorrow c xs ys).1 = true ↔
      bitValue xs < bitValue ys + (if c then 1 else 0) := by
  have hv := subtractWithBorrow_value c xs ys
  have hb := bitValue_lt_pow_length (subtractWithBorrow c xs ys).2
  have hb' : (bitValue (subtractWithBorrow c xs ys).2 : ℤ) <
      ((2 ^ (subtractWithBorrow c xs ys).2.length : ℕ) : ℤ) := Int.ofNat_lt.mpr hb
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hb'
  cases h : (subtractWithBorrow c xs ys).1 <;> cases c <;> simp_all <;> omega

/-- Raw binary comparison, computable with the same finite borrow register. -/
def lessBits (xs ys : List Bool) : Bool := (subtractWithBorrow false xs ys).1

@[simp] theorem lessBits_eq_true (xs ys : List Bool) :
    lessBits xs ys = true ↔ bitValue xs < bitValue ys := by
  simpa [lessBits] using subtractWithBorrow_borrow false xs ys

@[simp] theorem lessBits_encodeNat (m n : ℕ) :
    lessBits (Computability.encodeNat m) (Computability.encodeNat n) = decide (m < n) := by
  apply Bool.eq_iff_iff.mpr
  simp

/-- Truncated subtraction followed by canonical normalization. -/
def subBits (xs ys : List Bool) : List Bool :=
  let r := subtractWithBorrow false xs ys
  if r.1 then [] else normalizeBits r.2

/-- Correctness on arbitrary input words, including high-zero padding. -/
theorem subBits_eq_encode (xs ys : List Bool) :
    subBits xs ys = Computability.encodeNat (bitValue xs - bitValue ys) := by
  have hv := subtractWithBorrow_value false xs ys
  have hb := subtractWithBorrow_borrow false xs ys
  cases h : (subtractWithBorrow false xs ys).1 with
  | false =>
    simp only [subBits, h, Bool.false_eq_true, ↓reduceIte, normalizeBits_eq_encode]
    congr 1
    simp only [h, Bool.false_eq_true, ↓reduceIte, sub_zero] at hv
    omega
  | true =>
    have hlt : bitValue xs < bitValue ys := by simpa using hb.mp h
    have hz : bitValue xs - bitValue ys = 0 := by omega
    simp [subBits, h, hz, Computability.encodeNat, Computability.encodeNum]

@[simp] theorem subBits_encodeNat (m n : ℕ) :
    subBits (Computability.encodeNat m) (Computability.encodeNat n) =
      Computability.encodeNat (m - n) := by
  simpa using subBits_eq_encode (Computability.encodeNat m) (Computability.encodeNat n)

theorem normalizeBits_length_le (xs : List Bool) : (normalizeBits xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [normalizeBits, canonicalCons]
    split
    · cases b <;> simp
    · simp; omega

theorem subBits_length_le (xs ys : List Bool) :
    (subBits xs ys).length ≤ max xs.length ys.length := by
  dsimp [subBits]
  split
  · simp
  · exact (normalizeBits_length_le _).trans_eq (subtractWithBorrow_length false xs ys)

end PlanarHom.BinaryArithmetic
