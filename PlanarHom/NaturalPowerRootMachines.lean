import PlanarHom.NaturalPowerRootAlgorithm

/-! # Actual polynomial-time natural power-root machines

No root oracle is used: each bisection body is a finite circuit of the proved
binary addition, multiplication, division, comparison, and selection machines.
The iteration compiler substitutes those concrete machines on the complete
canonical transcript, and the loop runs for the binary input length.
-/

namespace PlanarHom.NaturalPowerRoot
open Complexity BinaryArithmetic ArithmeticCircuitPrimitives PairProjectionMachines
open MachineComposition Polynomial

def stateEncoding : BitEncoding SearchState :=
  BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)

theorem nat_length (a : ℕ) : (BitEncoding.nat.encode a).length = Nat.size a :=
  encodeNat_length a

theorem state_length (s : SearchState) :
    (stateEncoding.encode s).length =
      2 * Nat.size s.1 + 2 * Nat.size s.2.1 + Nat.size s.2.2 + 2 := by
  simp only [stateEncoding, BitEncoding.prod_length, nat_length]
  omega

theorem fp_natural_fixedPower (n : ℕ) : FP BitEncoding.nat BitEncoding.nat
    (fun a : ℕ => a^n) := by
  induction n with
  | zero => simpa using fp_const BitEncoding.nat BitEncoding.nat 1
  | succ n ih =>
    exact ((ih.pair (fp_id BitEncoding.nat)).comp fp_multiplication).congr
      (fun a => (pow_succ a n).symm)

theorem fp_midpoint : FP stateEncoding BitEncoding.nat midpoint := by
  have hp := fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hs := hp.comp fp_addition
  exact (((hs.pair (fp_const stateEncoding BitEncoding.nat 2)).comp fp_division).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)).congr (fun _ => rfl)

theorem fp_step (n : ℕ) : FP stateEncoding stateEncoding (step n) := by
  have ha := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hp := fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hlo := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hhi := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have htest := (ha.pair (fp_midpoint.comp (fp_natural_fixedPower n))).comp fp_comparison
  have hleft := ha.pair (hlo.pair fp_midpoint)
  have hright := ha.pair (fp_midpoint.pair hhi)
  exact ((htest.pair (hleft.pair hright)).comp
    (ConditionalMachines.fp_select stateEncoding)).congr (fun s => by simp [step])

theorem iterate_size (n k : ℕ) (s : SearchState) :
    (stateEncoding.encode ((step n)^[k] s)).length ≤ 3 * (stateEncoding.encode s).length := by
  obtain ⟨ha, hlo, hhi⟩ := iterate_bound n k s
  have hm : Nat.size (max s.2.1 s.2.2) ≤ Nat.size s.2.1 + Nat.size s.2.2 := by
    rcases le_total s.2.1 s.2.2 with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have hl := (Nat.size_le_size hlo).trans hm
  have hh := (Nat.size_le_size hhi).trans hm
  rw [state_length, state_length, ha]
  omega

noncomputable def iterateComputer (n : ℕ) :
    Turing.TM2ComputableInPolyTime (BitEncoding.unaryNat.prod stateEncoding).toFinEncoding
      stateEncoding.toFinEncoding (fun p => (step n)^[p.1] p.2) :=
  BoundedIterationMachine.computer stateEncoding (step n) (Classical.choice (fp_step n))
    (C 3 * X) (by
      intro k s i _
      have h := iterate_size n i s
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        BitEncoding.prod_length]
      omega)

theorem fp_initial : FP BitEncoding.nat stateEncoding initial := by
  exact ((fp_id BitEncoding.nat).pair ((fp_const BitEncoding.nat BitEncoding.nat 0).pair
    fp_successor)).congr (fun _ => rfl)

/-- The returned natural power root is computed by an actual polynomial-time
machine on the binary natural codec. The exponent is a fixed program parameter. -/
theorem fp_root (n : ℕ) : FP BitEncoding.nat BitEncoding.nat (root n) := by
  have hl : FP BitEncoding.nat BitEncoding.unaryNat Nat.size :=
    ⟨by simpa only [nat_length] using InputLengthMachine.computer BitEncoding.nat⟩
  have hi := (hl.pair fp_initial).comp (show FP _ _ _ from ⟨iterateComputer n⟩)
  exact (hi.comp ((fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).comp
    (fp_fst BitEncoding.nat BitEncoding.nat))).congr (fun _ => rfl)

end PlanarHom.NaturalPowerRoot
