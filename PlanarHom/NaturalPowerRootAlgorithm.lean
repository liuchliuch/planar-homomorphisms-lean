import PlanarHom.ArithmeticCircuitPrimitives
import PlanarHom.ConditionalMachines
import PlanarHom.BoundedIterationMachine
import PlanarHom.CodecSizeBounds

/-! # Binary bisection for a fixed natural power

The loop uses the binary input length as its iteration count. Its live natural
numbers never exceed the largest initial endpoint; this will allow compilation
to the project's actual finite-control bit machines.
-/

namespace PlanarHom.NaturalPowerRoot
open Complexity BinaryArithmetic ArithmeticCircuitPrimitives PairProjectionMachines

abbrev SearchState := ℕ × (ℕ × ℕ)

def midpoint (s : SearchState) : ℕ := (s.2.1 + s.2.2) / 2

def step (n : ℕ) (s : SearchState) : SearchState :=
  if s.1 < midpoint s ^ n then (s.1, s.2.1, midpoint s)
  else (s.1, midpoint s, s.2.2)

def initial (a : ℕ) : SearchState := (a, 0, a + 1)

def root (n a : ℕ) : ℕ := ((step n)^[Nat.size a] (initial a)).2.1

theorem midpoint_le_max (s : SearchState) : midpoint s ≤ max s.2.1 s.2.2 := by
  dsimp [midpoint]
  have h₁ := Nat.le_max_left s.2.1 s.2.2
  have h₂ := Nat.le_max_right s.2.1 s.2.2
  omega

theorem step_bound (n : ℕ) (s : SearchState) (B : ℕ)
    (hlo : s.2.1 ≤ B) (hhi : s.2.2 ≤ B) :
    (step n s).1 = s.1 ∧ (step n s).2.1 ≤ B ∧ (step n s).2.2 ≤ B := by
  have hm : midpoint s ≤ B := (midpoint_le_max s).trans (max_le hlo hhi)
  unfold step
  split <;> simp_all

theorem iterate_bound (n k : ℕ) (s : SearchState) :
    ((step n)^[k] s).1 = s.1 ∧
      ((step n)^[k] s).2.1 ≤ max s.2.1 s.2.2 ∧
      ((step n)^[k] s).2.2 ≤ max s.2.1 s.2.2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := step_bound n ((step n)^[k] s) _ ih.2.1 ih.2.2
    exact ⟨h.1.trans ih.1, h.2⟩

theorem step_brackets (n : ℕ) (hn : n ≠ 0) (s : SearchState) (x : ℕ)
    (hp : s.1 = x ^ n) (hlo : s.2.1 ≤ x) (hhi : x < s.2.2) :
    (step n s).1 = x ^ n ∧ (step n s).2.1 ≤ x ∧ x < (step n s).2.2 := by
  unfold step
  split_ifs with h
  · refine ⟨hp, hlo, ?_⟩
    exact lt_of_pow_lt_pow_left' n (hp ▸ h)
  · refine ⟨hp, ?_, hhi⟩
    exact (Nat.pow_le_pow_iff_left hn).mp (hp ▸ Nat.le_of_not_gt h)

theorem step_width (n k : ℕ) (s : SearchState)
    (horder : s.2.1 ≤ s.2.2) (hwidth : s.2.2 - s.2.1 ≤ 2 ^ (k+1)) :
    (step n s).2.2 - (step n s).2.1 ≤ 2 ^ k := by
  have hpow : 2 ^ (k+1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have hm := Nat.div_add_mod (s.2.1+s.2.2) 2
  have hr := Nat.mod_lt (s.2.1+s.2.2) (by decide : 0 < 2)
  unfold step midpoint
  split <;> simp only <;> omega

theorem iterate_brackets (n : ℕ) (hn : n ≠ 0) (x k : ℕ) :
    ((step n)^[k] (initial (x^n))).1 = x^n ∧
      ((step n)^[k] (initial (x^n))).2.1 ≤ x ∧
      x < ((step n)^[k] (initial (x^n))).2.2 := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, initial, Nat.zero_le, true_and]
    exact Nat.lt_succ_of_le (Nat.le_self_pow hn x)
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step_brackets n hn _ x ih.1 ih.2.1 ih.2.2

theorem iterate_width (n : ℕ) (hn : n ≠ 0) (x L k : ℕ)
    (hk : k ≤ L) (hL : x^n+1 ≤ 2^L) :
    ((step n)^[k] (initial (x^n))).2.2 -
      ((step n)^[k] (initial (x^n))).2.1 ≤ 2^(L-k) := by
  induction k with
  | zero => simpa [initial] using hL
  | succ k ih =>
    have hkl : k ≤ L := by omega
    have hi := ih hkl
    have hb := iterate_brackets n hn x k
    have he : L-k = (L-(k+1))+1 := by omega
    rw [Function.iterate_succ_apply']
    exact step_width n (L-(k+1)) _ (by omega) (he ▸ hi)

/-- Exact recovery from a perfect power, including zero. -/
theorem root_pow (n : ℕ) (hn : n ≠ 0) (x : ℕ) : root n (x^n) = x := by
  have hb := iterate_brackets n hn x (Nat.size (x^n))
  have hw := iterate_width n hn x (Nat.size (x^n)) (Nat.size (x^n))
    (by rfl) (Nat.lt_size_self (x^n))
  simp only [Nat.sub_self, pow_zero] at hw
  unfold root
  omega

end PlanarHom.NaturalPowerRoot
