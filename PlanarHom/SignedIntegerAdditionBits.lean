import PlanarHom.RationalMultiplicationBits

/-! # Signed-index binary addition via finite two's-complement carry gates -/
namespace PlanarHom.BinaryArithmetic

def intWordValue (sign : Bool) (xs : List Bool) : ℤ :=
  if sign then -(bitValue xs : ℤ)-1 else bitValue xs

def twosValue (sign : Bool) (xs : List Bool) : ℤ :=
  (bitValue xs : ℤ) - (if sign then (2:ℤ)^xs.length else 0)

/-- An absent unsigned-index bit is a sign-extension bit after XOR. -/
theorem intWordValue_expand (sign : Bool) (xs : List Bool) :
    intWordValue sign xs = (if xor (xs.head?.getD false) sign then 1 else 0) +
      2*intWordValue sign xs.tail := by
  cases xs with
  | nil => cases sign <;> simp [intWordValue,bitValue]
  | cons b xs =>
    cases b <;> cases sign <;> simp [intWordValue,bitValue]
    all_goals omega

theorem twosValue_cons (sign bit : Bool) (xs : List Bool) :
    twosValue sign (bit::xs) = (if bit then 1 else 0) + 2*twosValue sign xs := by
  cases sign <;> cases bit <;> simp [twosValue,bitValue,pow_succ]
  all_goals ring

theorem fullAdder_value (x y c : Bool) :
    (if fullAdderBit x y c then (1:ℤ) else 0) +
      2*(if fullAdderCarry x y c then 1 else 0) =
        (if x then 1 else 0)+(if y then 1 else 0)+(if c then 1 else 0) := by
  cases x <;> cases y <;> cases c <;> decide

/-- One extra sign-extension position suffices to establish the stable result
sign after the finite input words are exhausted. -/
def twosAdd (sa sb carry : Bool) (xs ys : List Bool) : Bool × List Bool :=
  match xs,ys with
  | [],[] => (fullAdderBit sa sb (fullAdderCarry sa sb carry),[fullAdderBit sa sb carry])
  | x::xs,[] =>
    let r := twosAdd sa sb (fullAdderCarry (xor x sa) sb carry) xs []
    (r.1,fullAdderBit (xor x sa) sb carry :: r.2)
  | [],y::ys =>
    let r := twosAdd sa sb (fullAdderCarry sa (xor y sb) carry) [] ys
    (r.1,fullAdderBit sa (xor y sb) carry :: r.2)
  | x::xs,y::ys =>
    let r := twosAdd sa sb (fullAdderCarry (xor x sa) (xor y sb) carry) xs ys
    (r.1,fullAdderBit (xor x sa) (xor y sb) carry :: r.2)
termination_by xs.length+ys.length

theorem twosAdd_step (sa sb c : Bool) (xs ys : List Bool) (h : xs≠[] ∨ ys≠[]) :
    twosAdd sa sb c xs ys =
      let x := xor (xs.head?.getD false) sa
      let y := xor (ys.head?.getD false) sb
      let r := twosAdd sa sb (fullAdderCarry x y c) xs.tail ys.tail
      (r.1,fullAdderBit x y c :: r.2) := by
  cases xs <;> cases ys <;> simp_all only [twosAdd,List.head?_nil,List.head?_cons,
    Option.getD_none,Option.getD_some,List.tail_nil,List.tail_cons,Bool.false_xor,ne_eq,not_true_eq_false,or_self]

/-- Exact signed addition, with no numeric arithmetic instruction in the program. -/
theorem twosAdd_value (sa sb c : Bool) (xs ys : List Bool) :
    twosValue (twosAdd sa sb c xs ys).1 (twosAdd sa sb c xs ys).2 =
      intWordValue sa xs + intWordValue sb ys + (if c then 1 else 0) := by
  by_cases h : xs=[] ∧ ys=[]
  · rcases h with ⟨rfl,rfl⟩
    cases sa <;> cases sb <;> cases c <;>
      simp [twosAdd,twosValue,intWordValue,bitValue,fullAdderBit,fullAdderCarry]
  · have hn : xs≠[] ∨ ys≠[] := by tauto
    rw [twosAdd_step sa sb c xs ys hn]
    dsimp only
    rw [twosValue_cons,twosAdd_value sa sb
      (fullAdderCarry (xor (xs.head?.getD false) sa) (xor (ys.head?.getD false) sb) c) xs.tail ys.tail]
    have hg := fullAdder_value (xor (xs.head?.getD false) sa) (xor (ys.head?.getD false) sb) c
    conv_rhs => rw [intWordValue_expand sa xs,intWordValue_expand sb ys]
    omega
termination_by xs.length+ys.length
decreasing_by
  have hn : xs≠[] ∨ ys≠[] := by tauto
  cases xs <;> cases ys <;> simp_all
  omega

theorem bitValue_complement (xs : List Bool) :
    bitValue (xs.map (fun b => xor b true)) + bitValue xs + 1 = 2^xs.length := by
  induction xs with
  | nil => simp [bitValue]
  | cons b xs ih =>
    cases b <;> simp only [List.map_cons,bitValue,List.length_cons,pow_succ,
      Bool.false_xor,Bool.true_xor,Bool.not_true,Bool.false_eq_true,↓reduceIte]
    all_goals omega

theorem intWordValue_xor (sign : Bool) (xs : List Bool) :
    intWordValue sign (xs.map (fun b => xor b sign)) = twosValue sign xs := by
  cases sign with
  | false => simp [intWordValue,twosValue]
  | true =>
    have h := congrArg (fun n:ℕ => (n:ℤ)) (bitValue_complement xs)
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] at h
    simp only [intWordValue,twosValue,↓reduceIte]
    omega

theorem intWordValue_eq_signedIndex (sign : Bool) (xs : List Bool) :
    intWordValue sign xs = signedIndex sign (bitValue xs) := by
  cases sign <;> simp [intWordValue,signedIndex,Int.negSucc_eq]
  omega

@[simp] theorem intWordValue_encodeNat (sign : Bool) (n : ℕ) :
    intWordValue sign (Computability.encodeNat n) = signedIndex sign n := by
  rw [intWordValue_eq_signedIndex,bitValue_encodeNat]

def intWordOutput (sign : Bool) (xs : List Bool) : List Bool :=
  Complexity.BitEncoding.frame [sign] ++ normalizeBits (xs.map (fun b => xor b sign))

/-- High-zero trimming after sign XOR produces the exact constructor-index code. -/
theorem intWordOutput_correct (sign : Bool) (xs : List Bool) :
    intWordOutput sign xs = Complexity.BitEncoding.int.encode (twosValue sign xs) := by
  have hcode (n:ℕ) : Complexity.BitEncoding.int.encode (signedIndex sign n) =
      Complexity.BitEncoding.frame [sign] ++ Computability.encodeNat n := by cases sign <;> rfl
  unfold intWordOutput
  rw [normalizeBits_eq_encode,← hcode]
  congr 1
  rw [← intWordValue_eq_signedIndex,intWordValue_xor]

/-- The output of the bit-level full-adder is the canonical sum of two integers. -/
theorem intWordOutput_add_encode (sa sb : Bool) (a b : ℕ) :
    intWordOutput (twosAdd sa sb false (Computability.encodeNat a) (Computability.encodeNat b)).1
      (twosAdd sa sb false (Computability.encodeNat a) (Computability.encodeNat b)).2 =
        Complexity.BitEncoding.int.encode (signedIndex sa a + signedIndex sb b) := by
  rw [intWordOutput_correct,twosAdd_value]
  simp

end PlanarHom.BinaryArithmetic
