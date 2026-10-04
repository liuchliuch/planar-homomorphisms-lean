import PlanarHom.BinaryArithmetic

namespace PlanarHom.BinaryArithmetic

/-- The low output bit of a binary full adder. -/
def fullAdderBit (x y carry : Bool) : Bool := xor (xor x y) carry

/-- The majority bit is the carry out of a binary full adder. -/
def fullAdderCarry (x y carry : Bool) : Bool :=
  (x && y) || (x && carry) || (y && carry)

/-- Little-endian full-adder recursion, with absent input bits padded by zero.
Only a nonzero final carry is emitted after both input lists are exhausted. -/
def addBits (carry : Bool) (xs ys : List Bool) : List Bool :=
  match xs, ys with
  | [], [] => if carry then [true] else []
  | x :: xs, [] =>
      fullAdderBit x false carry :: addBits (fullAdderCarry x false carry) xs []
  | [], y :: ys =>
      fullAdderBit false y carry :: addBits (fullAdderCarry false y carry) [] ys
  | x :: xs, y :: ys =>
      fullAdderBit x y carry :: addBits (fullAdderCarry x y carry) xs ys
termination_by xs.length + ys.length

@[simp] theorem addBits_nil_left (carry : Bool) (ys : List Bool) :
    addBits carry [] ys = if carry then succBits ys else ys := by
  induction ys generalizing carry with
  | nil => cases carry <;> simp [addBits, succBits]
  | cons y ys ih =>
    cases carry <;> cases y <;> simp [addBits, fullAdderBit, fullAdderCarry, succBits, ih]

@[simp] theorem addBits_nil_right (carry : Bool) (xs : List Bool) :
    addBits carry xs [] = if carry then succBits xs else xs := by
  induction xs generalizing carry with
  | nil => cases carry <;> simp [succBits]
  | cons x xs ih =>
    cases carry <;> cases x <;> simp [addBits, fullAdderBit, fullAdderCarry, succBits, ih]

/-- Adding a carry computes successor after adding the represented positives. -/
theorem addBits_encodePosNum (carry : Bool) (m n : PosNum) :
    addBits carry (Computability.encodePosNum m) (Computability.encodePosNum n) =
      Computability.encodePosNum (if carry then (m + n).succ else m + n) := by
  induction m generalizing carry n with
  | one =>
    cases n <;> cases carry <;>
      simp [Computability.encodePosNum, addBits, fullAdderBit, fullAdderCarry,
        HAdd.hAdd, Add.add, PosNum.add, PosNum.succ, succBits]
  | bit0 m ih =>
    cases n <;> cases carry <;>
      simp [Computability.encodePosNum, addBits, fullAdderBit, fullAdderCarry,
        HAdd.hAdd, Add.add, PosNum.add, PosNum.succ, ih]
  | bit1 m ih =>
    cases n <;> cases carry <;>
      simp [Computability.encodePosNum, addBits, fullAdderBit, fullAdderCarry,
        HAdd.hAdd, Add.add, PosNum.add, PosNum.succ, ih]

/-- Full-adder correctness for the canonical binary natural-number type. -/
theorem addBits_encodeNum (carry : Bool) (m n : Num) :
    addBits carry (Computability.encodeNum m) (Computability.encodeNum n) =
      Computability.encodeNum (if carry then (m + n).succ else m + n) := by
  cases m <;> cases n <;> cases carry <;>
    simp [Computability.encodeNum, HAdd.hAdd, Add.add, Num.add, Num.succ,
      Num.succ', addBits_encodePosNum, succBits]
  rfl

/-- The carry input represents precisely an extra one. -/
theorem addBits_encodeNat_carry (carry : Bool) (m n : ℕ) :
    addBits carry (Computability.encodeNat m) (Computability.encodeNat n) =
      Computability.encodeNat (m + n + if carry then 1 else 0) := by
  cases carry <;>
    simp [Computability.encodeNat, addBits_encodeNum, Nat.cast_add, Num.add_one]

/-- Binary addition produces exactly the canonical encoding of the sum. -/
@[simp] theorem addBits_encodeNat (m n : ℕ) :
    addBits false (Computability.encodeNat m) (Computability.encodeNat n) =
      Computability.encodeNat (m + n) := by
  simpa using addBits_encodeNat_carry false m n

/-- The output has at most one more bit than the longer input. -/
theorem addBits_length_le_max (carry : Bool) (xs ys : List Bool) :
    (addBits carry xs ys).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing carry ys with
  | nil =>
    cases carry
    · simp
    · simpa using succBits_length_le ys
  | cons x xs ih =>
    cases ys with
    | nil =>
      cases carry
      · simp
      · simpa using succBits_length_le (x :: xs)
    | cons y ys =>
      have h := ih (fullAdderCarry x y carry) ys
      simp only [addBits, List.length_cons]
      omega

/-- A convenient additive upper bound for binary addition's output length. -/
theorem addBits_length_le (carry : Bool) (xs ys : List Bool) :
    (addBits carry xs ys).length ≤ xs.length + ys.length + 1 := by
  have h := addBits_length_le_max carry xs ys
  omega

end PlanarHom.BinaryArithmetic
