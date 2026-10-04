import PlanarHom.BinarySubtractionBits
import Mathlib.Tactic.Ring

/-! # Most-significant-bit-first binary long division -/
namespace PlanarHom.BinaryArithmetic

/-- Numerical form of the long-division recurrence, used only in its proof. -/
def divNatLoop (d : ℕ) (ms : List Bool) (q r : ℕ) : ℕ × ℕ :=
  match ms with
  | [] => (q, r)
  | b :: ms =>
    let s := (if b then 1 else 0) + 2*r
    if s < d then divNatLoop d ms (2*q) s
    else divNatLoop d ms (1+2*q) (s-d)

/-- Each most-significant-first bit invokes at most one binary subtraction. -/
def divLoop (ds ms qs rs : List Bool) : List Bool × List Bool :=
  match ms with
  | [] => (qs, rs)
  | b :: ms =>
    let shifted := canonicalCons b rs
    let underflow := lessBits shifted ds
    divLoop ds ms (canonicalCons (!underflow) qs)
      (if underflow then shifted else subBits shifted ds)

/-- Zero divisors use Lean's total natural-number division convention. -/
def divBits (xs ds : List Bool) : List Bool × List Bool :=
  if ds = [] then ([], xs) else divLoop ds xs.reverse [] []

@[simp] theorem encodeNat_eq_nil (n : ℕ) : Computability.encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := bitValue_encodeNat n
    rw [h] at hv
    exact hv.symm
  · rintro rfl
    simp [Computability.encodeNat, Computability.encodeNum]

/-- Canonical code preservation for every long-division iteration. -/
theorem divLoop_encodeNat (d : ℕ) (ms : List Bool) (q r : ℕ) :
    divLoop (Computability.encodeNat d) ms (Computability.encodeNat q) (Computability.encodeNat r) =
      ((Computability.encodeNat (divNatLoop d ms q r).1),
        (Computability.encodeNat (divNatLoop d ms q r).2)) := by
  induction ms generalizing q r with
  | nil => rfl
  | cons b ms ih =>
    simp only [divLoop, canonicalCons_encodeNat, lessBits_encodeNat]
    by_cases h : (if b then 1 else 0) + 2*r < d
    · simp [h, divNatLoop, ih]
    · simp [h, divNatLoop, subBits_encodeNat, ih]

/-- A significant-bit stream records the Horner value of its reversed word. -/
theorem bitValue_append_singleton (xs : List Bool) (b : Bool) :
    bitValue (xs ++ [b]) = bitValue xs + (if b then 1 else 0)*2^xs.length := by
  induction xs with
  | nil => simp [bitValue]
  | cons x xs ih =>
    simp only [List.cons_append, bitValue, List.length_cons, ih, pow_succ]
    ring

/-- The standard division invariant: a bounded remainder and an exact dividend
identity. No assumption of division correctness is built into the recurrence. -/
theorem divNatLoop_invariant (d : ℕ) (ms : List Bool) (q r : ℕ) (hr : r < d) :
    (divNatLoop d ms q r).2 < d ∧
      (divNatLoop d ms q r).1*d + (divNatLoop d ms q r).2 =
        (q*d+r)*2^ms.length + bitValue ms.reverse := by
  induction ms generalizing q r with
  | nil => simp [divNatLoop, bitValue, hr]
  | cons b ms ih =>
    let s := (if b then 1 else 0) + 2*r
    have hsmall : s < 2*d := by dsimp [s]; cases b <;> simp_all; omega
    have finish (q' r' : ℕ) (hr' : r' < d)
        (hid : q'*d+r' = 2*(q*d+r)+(if b then 1 else 0)) :
        (divNatLoop d ms q' r').2 < d ∧
          (divNatLoop d ms q' r').1*d + (divNatLoop d ms q' r').2 =
            (q*d+r)*2^(b :: ms).length + bitValue (b :: ms).reverse := by
      have hh := ih q' r' hr'
      refine ⟨hh.1, ?_⟩
      rw [hh.2, hid]
      simp only [List.length_cons, List.reverse_cons, bitValue_append_singleton,
        List.length_reverse, pow_succ]
      ring
    by_cases hs : s < d
    · simp only [divNatLoop, show ((if b then 1 else 0) + 2*r < d) from hs, ↓reduceIte]
      apply finish (2*q) s hs
      dsimp [s]
      ring
    · have hds : d ≤ s := by omega
      have hr' : s-d < d := by omega
      have hid : (1+2*q)*d+(s-d) = 2*(q*d+r)+(if b then 1 else 0) := by
        have he : s-d+d=s := Nat.sub_add_cancel hds
        dsimp [s] at he
        rw [Nat.add_mul]
        simp only [Nat.one_mul, Nat.mul_assoc] at *
        omega
      simpa only [divNatLoop, show ¬((if b then 1 else 0) + 2*r < d) from hs, ↓reduceIte]
        using finish (1+2*q) (s-d) hr' hid

/-- Exact quotient and remainder of the original canonical input. -/
@[simp] theorem divBits_encodeNat (n d : ℕ) :
    divBits (Computability.encodeNat n) (Computability.encodeNat d) =
      (Computability.encodeNat (n/d), Computability.encodeNat (n%d)) := by
  by_cases hd : d = 0
  · subst d
    simp [divBits, Computability.encodeNat, Computability.encodeNum]
  · have hdpos : 0 < d := by omega
    have h := divNatLoop_invariant d (Computability.encodeNat n).reverse 0 0 hdpos
    simp only [Nat.zero_mul, Nat.zero_add, List.reverse_reverse, bitValue_encodeNat] at h
    have hv : n / d = (divNatLoop d (Computability.encodeNat n).reverse 0 0).1 ∧
        n % d = (divNatLoop d (Computability.encodeNat n).reverse 0 0).2 := by
      apply (Nat.div_mod_unique hdpos).2
      exact ⟨by simpa [Nat.add_comm, Nat.mul_comm] using h.2, h.1⟩
    have he := divLoop_encodeNat d (Computability.encodeNat n).reverse 0 0
    have hz : Computability.encodeNat 0 = [] := (encodeNat_eq_nil 0).2 rfl
    rw [hz, ← hv.1, ← hv.2] at he
    simpa [divBits, hd] using he

/-- Canonical-cons never grows a word by more than one bit. -/
theorem canonicalCons_length_le (b : Bool) (xs : List Bool) :
    (canonicalCons b xs).length ≤ xs.length + 1 := by
  cases b <;> simp
  exact shiftBits_length_le xs

/-- Input-size bounds sufficient for the machine's uniform loop-time invariant. -/
theorem divLoop_length_le (ds ms qs rs : List Bool) :
    (divLoop ds ms qs rs).1.length ≤ qs.length + ms.length ∧
      (divLoop ds ms qs rs).2.length ≤ max rs.length ds.length + ms.length := by
  induction ms generalizing qs rs with
  | nil => simp [divLoop]
  | cons b ms ih =>
    let shifted := canonicalCons b rs
    let underflow := lessBits shifted ds
    have hs := canonicalCons_length_le b rs
    have hq := canonicalCons_length_le (!underflow) qs
    have hr : (if underflow then shifted else subBits shifted ds).length ≤
        max rs.length ds.length + 1 := by
      cases hu : underflow
      · have hsub := subBits_length_le shifted ds
        simp only [Bool.false_eq_true, ↓reduceIte]
        dsimp [shifted] at hsub ⊢
        omega
      · simp only [↓reduceIte]
        dsimp [shifted]
        omega
    have hh := ih (canonicalCons (!underflow) qs)
      (if underflow then shifted else subBits shifted ds)
    change (divLoop ds ms (canonicalCons (!underflow) qs)
      (if underflow then shifted else subBits shifted ds)).1.length ≤ _ ∧
      (divLoop ds ms (canonicalCons (!underflow) qs)
        (if underflow then shifted else subBits shifted ds)).2.length ≤ _
    simp only [List.length_cons]
    constructor <;> omega

end PlanarHom.BinaryArithmetic
