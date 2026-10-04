import PlanarHom.BinaryDivisionBits

/-! # Bit-length and Euclidean-descent bounds for binary gcd -/
namespace PlanarHom.BinaryArithmetic

@[simp] theorem encodePosNum_length (n : PosNum) :
    (Computability.encodePosNum n).length = n.natSize := by
  induction n <;> simp_all [Computability.encodePosNum, PosNum.natSize]

@[simp] theorem encodeNum_length (n : Num) :
    (Computability.encodeNum n).length = n.natSize := by
  cases n <;> simp [Computability.encodeNum, Num.natSize]

/-- The actual code length is the usual binary bit length. -/
@[simp] theorem encodeNat_length (n : ℕ) :
    (Computability.encodeNat n).length = Nat.size n := by
  simp [Computability.encodeNat, Num.natSize_to_nat]

theorem encodeNat_length_mono {m n : ℕ} (h : m ≤ n) :
    (Computability.encodeNat m).length ≤ (Computability.encodeNat n).length := by
  simpa using Nat.size_le_size h

/-- Every two nontrivial Euclidean remainder steps halve the smaller operand. -/
theorem euclidean_two_step_halving (a b : ℕ) (hb : 0 < b) (hrpos : 0 < a % b) :
    2 * (b % (a % b)) < b := by
  have hrlt := Nat.mod_lt a hb
  by_cases hh : 2 * (a % b) ≤ b
  · have hm := Nat.mod_lt b hrpos
    omega
  · have hle : a % b ≤ b := by omega
    have hdiff : b - a % b < a % b := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hdiff]
    omega

/-- Two Euclidean steps remove at least one bit from a power-of-two bound. -/
theorem euclidean_two_step_pow (a b k : ℕ) (hb : 0 < b) (hr : 0 < a % b) (hk : b < 2^(k+1)) :
    b % (a % b) < 2^k := by
  have h := euclidean_two_step_halving a b hb hr
  rw [pow_succ] at hk
  omega

/-- The usual Euclidean invariant, oriented for the implemented pair update. -/
theorem gcd_euclidean_step (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a%b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]

end PlanarHom.BinaryArithmetic
