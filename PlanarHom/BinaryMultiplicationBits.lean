import PlanarHom.BinaryAdditionBits

/-! # Canonical binary shift and shift-add multiplication -/
namespace PlanarHom.BinaryArithmetic

/-- Left-shift preserving the unique empty representation of zero. -/
def shiftBits (xs : List Bool) : List Bool := if xs = [] then [] else false :: xs

@[simp] theorem shiftBits_nil : shiftBits [] = [] := rfl
@[simp] theorem shiftBits_cons (b : Bool) (xs : List Bool) :
    shiftBits (b :: xs) = false :: b :: xs := by simp [shiftBits]

theorem shiftBits_length_le (xs : List Bool) : (shiftBits xs).length ≤ xs.length + 1 := by
  cases xs <;> simp

@[simp] theorem shiftBits_encodeNum (n : Num) :
    shiftBits (Computability.encodeNum n) = Computability.encodeNum n.bit0 := by
  cases n with
  | zero => rfl
  | pos n =>
    simp [shiftBits, Computability.encodeNum, Computability.encodePosNum_nonempty,
      Num.bit0, Computability.encodePosNum]

@[simp] theorem shiftBits_encodeNat (n : ℕ) :
    shiftBits (Computability.encodeNat n) = Computability.encodeNat (2 * n) := by
  simp [Computability.encodeNat, two_mul, Num.bit0_of_bit0]

/-- Numerical value of any little-endian word, allowing redundant high zeroes. -/
def bitValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitValue bs

@[simp] theorem bitValue_encodePosNum (n : PosNum) :
    bitValue (Computability.encodePosNum n) = (n : ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih => simp [Computability.encodePosNum, bitValue, ih, PosNum.cast_bit0, two_mul]
  | bit1 n ih => simp [Computability.encodePosNum, bitValue, ih, PosNum.cast_bit1, two_mul, Nat.add_assoc, Nat.add_comm]

@[simp] theorem bitValue_encodeNum (n : Num) :
    bitValue (Computability.encodeNum n) = (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos n => exact bitValue_encodePosNum n

@[simp] theorem bitValue_encodeNat (n : ℕ) : bitValue (Computability.encodeNat n) = n := by
  simp [Computability.encodeNat]

/-- Shift-and-add multiplication with an explicit accumulator. -/
def mulLoop (xs ys zs : List Bool) : List Bool :=
  match ys with
  | [] => zs
  | b :: bs => mulLoop (shiftBits xs) bs (if b then addBits false xs zs else zs)

def mulBits (xs ys : List Bool) : List Bool := mulLoop xs ys []

/-- Every iteration preserves canonical encodings of the multiplicand and
accumulator, including when the multiplier has redundant high zeroes. -/
theorem mulLoop_encodeNat (m a : ℕ) (ys : List Bool) :
    mulLoop (Computability.encodeNat m) ys (Computability.encodeNat a) =
      Computability.encodeNat (m * bitValue ys + a) := by
  induction ys generalizing m a with
  | nil => simp [mulLoop, bitValue]
  | cons b ys ih =>
    cases b <;> simp only [mulLoop, Bool.false_eq_true, ↓reduceIte,
      shiftBits_encodeNat, addBits_encodeNat, ih, bitValue]
    · congr 1; simp [Nat.mul_assoc, Nat.mul_comm]
    · congr 1; simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem mulBits_encodeNat (m n : ℕ) :
    mulBits (Computability.encodeNat m) (Computability.encodeNat n) =
      Computability.encodeNat (m * n) := by
  have h := mulLoop_encodeNat m 0 (Computability.encodeNat n)
  rw [bitValue_encodeNat, Nat.add_zero] at h
  have hz : Computability.encodeNat 0 = [] := by
    simp [Computability.encodeNat, Computability.encodeNum]
  rw [hz] at h
  exact h

/-- Both data words can grow by at most one bit per multiplier bit. -/
theorem mulLoop_length_le (xs ys zs : List Bool) :
    (mulLoop xs ys zs).length ≤ max xs.length zs.length + ys.length := by
  induction ys generalizing xs zs with
  | nil => simp [mulLoop]
  | cons b ys ih =>
    have hx := shiftBits_length_le xs
    cases b with
    | false =>
      have h := ih (shiftBits xs) zs
      simp only [mulLoop, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    | true =>
      have h := ih (shiftBits xs) (addBits false xs zs)
      have ha := addBits_length_le_max false xs zs
      simp only [mulLoop, ↓reduceIte, List.length_cons]
      omega

theorem mulBits_length_le (xs ys : List Bool) :
    (mulBits xs ys).length ≤ xs.length + ys.length := by
  simpa [mulBits] using mulLoop_length_le xs ys []

end PlanarHom.BinaryArithmetic
