import PlanarHom.IntervalBisectionAlgorithm

/-! # Actual bit-machine compilation of bounded lower-bound search

The predicate is supplied as an actual FP machine on canonical typed inputs.
It is substituted into the finite-control loop; it is not retained as an oracle.
-/

namespace PlanarHom.IntervalBisection
open Complexity BinaryArithmetic ArithmeticCircuitPrimitives PairProjectionMachines
open MachineComposition Polynomial

def stateEncoding {α : Type} (ea : BitEncoding α) : BitEncoding (State α) :=
  ea.prod (BitEncoding.nat.prod BitEncoding.nat)

theorem state_length {α : Type} (ea : BitEncoding α) (s : State α) :
    ((stateEncoding ea).encode s).length =
      2*(ea.encode s.1).length+2*Nat.size s.2.1+Nat.size s.2.2+2 := by
  simp only [stateEncoding, BitEncoding.prod_length, NaturalPowerRoot.nat_length]
  omega

theorem fp_midpoint {α : Type} (ea : BitEncoding α) :
    FP (stateEncoding ea) BitEncoding.nat midpoint := by
  have hs := (fp_snd ea (BitEncoding.nat.prod BitEncoding.nat)).comp fp_addition
  exact (((hs.pair (fp_const (stateEncoding ea) BitEncoding.nat 2)).comp fp_division).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)).congr (fun _ => rfl)

theorem fp_step {α : Type} (ea : BitEncoding α) (test : α → ℕ → Bool)
    (htest : FP (ea.prod BitEncoding.nat) BitEncoding.bool (fun p => test p.1 p.2)) :
    FP (stateEncoding ea) (stateEncoding ea) (step test) := by
  have hx := fp_fst ea (BitEncoding.nat.prod BitEncoding.nat)
  have hp := fp_snd ea (BitEncoding.nat.prod BitEncoding.nat)
  have hlo := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hhi := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hg := (hlo.pair hhi).comp fp_comparison
  have hm := fp_midpoint ea
  have ht := (hx.pair hm).comp htest
  have hl := hx.pair (hlo.pair hm)
  have hr := hx.pair ((hm.comp fp_successor).pair hhi)
  have hbranch := (ht.pair (hl.pair hr)).comp (ConditionalMachines.fp_select (stateEncoding ea))
  exact ((hg.pair (hbranch.pair (fp_id (stateEncoding ea)))).comp
    (ConditionalMachines.fp_select (stateEncoding ea))).congr (fun s => by simp [step])

theorem iterate_size {α : Type} (ea : BitEncoding α) (test : α → ℕ → Bool)
    (k : ℕ) (s : State α) :
    ((stateEncoding ea).encode ((step test)^[k] s)).length ≤
      3*((stateEncoding ea).encode s).length := by
  obtain ⟨hx, hlo, hhi⟩ := iterate_bound test k s
  have hm : Nat.size (max s.2.1 s.2.2) ≤ Nat.size s.2.1+Nat.size s.2.2 := by
    rcases le_total s.2.1 s.2.2 with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have hl := (Nat.size_le_size hlo).trans hm
  have hh := (Nat.size_le_size hhi).trans hm
  rw [state_length, state_length, hx]
  omega

noncomputable def iterateComputer {α : Type} (ea : BitEncoding α)
    (test : α → ℕ → Bool)
    (htest : FP (ea.prod BitEncoding.nat) BitEncoding.bool (fun p => test p.1 p.2)) :
    Turing.TM2ComputableInPolyTime (BitEncoding.unaryNat.prod (stateEncoding ea)).toFinEncoding
      (stateEncoding ea).toFinEncoding (fun p => (step test)^[p.1] p.2) :=
  BoundedIterationMachine.computer (stateEncoding ea) (step test)
    (Classical.choice (fp_step ea test htest)) (C 3*X) (by
      intro k s i _
      have h := iterate_size ea test i s
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        BitEncoding.prod_length]
      omega)

/-- Actual FP binary search on a possibly exponentially large finite interval. -/
theorem fp_cut {α : Type} (ea : BitEncoding α) (test : α → ℕ → Bool)
    (htest : FP (ea.prod BitEncoding.nat) BitEncoding.bool (fun p => test p.1 p.2)) :
    FP (ea.prod BitEncoding.nat) BitEncoding.nat (fun p => cut test p.1 p.2) := by
  have hx := fp_fst ea BitEncoding.nat
  have hn := (fp_snd ea BitEncoding.nat).comp fp_successor
  have hl : FP (ea.prod BitEncoding.nat) BitEncoding.unaryNat
      (fun p => Nat.size (p.2+1)) :=
    hn.comp ⟨by simpa only [NaturalPowerRoot.nat_length] using
      InputLengthMachine.computer BitEncoding.nat⟩
  have hi := hx.pair ((fp_const (ea.prod BitEncoding.nat) BitEncoding.nat 0).pair hn)
  have hs := (hl.pair hi).comp (show FP _ _ _ from ⟨iterateComputer ea test htest⟩)
  exact (hs.comp ((fp_snd ea (BitEncoding.nat.prod BitEncoding.nat)).comp
    (fp_fst BitEncoding.nat BitEncoding.nat))).congr (fun _ => rfl)

end PlanarHom.IntervalBisection
