import PlanarHom.Complexity
import Mathlib.Data.Num.Lemmas

/-!
# Bit-level arithmetic on actual finite-control stack machines

Successor is implemented by a fixed two-stack TM2 program, including restoring
its scratch stack and finite-control register. Its running time is linear in
the length of the binary input, not in the represented natural number.
-/

namespace PlanarHom.BinaryArithmetic

open Turing Turing.TM2

/-- Carry propagation on little-endian bit strings. -/
def succBits : List Bool → List Bool
  | [] => [true]
  | false :: xs => true :: xs
  | true :: xs => false :: succBits xs

@[simp] theorem succBits_encodePosNum (n : PosNum) :
    succBits (Computability.encodePosNum n) = Computability.encodePosNum n.succ := by
  induction n with
  | one => rfl
  | bit0 n ih => rfl
  | bit1 n ih => simp [Computability.encodePosNum, PosNum.succ, succBits, ih]

@[simp] theorem succBits_encodeNum (n : Num) :
    succBits (Computability.encodeNum n) = Computability.encodeNum n.succ := by
  cases n with
  | zero => rfl
  | pos n => exact succBits_encodePosNum n

@[simp] theorem succBits_encodeNat (n : ℕ) :
    succBits (Computability.encodeNat n) = Computability.encodeNat (n + 1) := by
  simp only [Computability.encodeNat, succBits_encodeNum, Nat.cast_add, Nat.cast_one,
    Num.add_one]

/-- The carry prefix cannot add more than one output bit. -/
theorem succBits_length_le (xs : List Bool) : (succBits xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => decide
  | cons b xs ih => cases b <;> simp_all [succBits]

/-- `false` is the input/output stack; `true` is a scratch stack. The two
labels are carry propagation and restoration. -/
def successorMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Option Bool
  initialState := none
  m
    | false => .pop false (fun _ b => b) <|
        .branch (fun b => b == some true)
          (.push true (fun _ => false) (.goto (fun _ => false)))
          (.push false (fun _ => true) (.goto (fun _ => true)))
    | true => .pop true (fun _ b => b) <|
        .branch Option.isSome
          (.push false (fun b => b.getD false) (.goto (fun _ => true)))
          (.load (fun _ => none) .halt)

/-- Concrete configurations expose both stack contents. -/
def succCfg (label : Option Bool) (v : Option Bool) (xs ys : List Bool) :
    successorMachine.Cfg :=
  ⟨label, v, fun k : Bool => cond k ys xs⟩

@[simp] theorem successor_step_carry_true (v) (xs ys : List Bool) :
    successorMachine.step (succCfg (some false) v (true :: xs) ys) =
      some (succCfg (some false) (some true) xs (false :: ys)) := by
  simp [successorMachine, succCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem successor_step_carry_false (v) (xs ys : List Bool) :
    successorMachine.step (succCfg (some false) v (false :: xs) ys) =
      some (succCfg (some true) (some false) (true :: xs) ys) := by
  simp [successorMachine, succCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem successor_step_carry_nil (v) (ys : List Bool) :
    successorMachine.step (succCfg (some false) v [] ys) =
      some (succCfg (some true) none [true] ys) := by
  simp [successorMachine, succCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem successor_step_restore_cons (v) (b : Bool) (xs ys : List Bool) :
    successorMachine.step (succCfg (some true) v xs (b :: ys)) =
      some (succCfg (some true) (some b) (b :: xs) ys) := by
  simp [successorMachine, succCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem successor_step_restore_nil (v) (xs : List Bool) :
    successorMachine.step (succCfg (some true) v xs []) =
      some (succCfg none none xs []) := by
  simp [successorMachine, succCfg, step, stepAux]

/-- A single real machine step is a one-step bounded execution. -/
def oneStep {α : Type} (f : α → Option α) {a b : α} (h : f a = some b) :
    EvalsToInTime f a (some b) 1 :=
  ⟨⟨1, h⟩, Nat.le_refl 1⟩

/-- A larger time budget preserves the very same execution. -/
def weakenTime {α : Type} {f : α → Option α} {a : α} {b : Option α} {n m : ℕ}
    (h : EvalsToInTime f a b n) (hn : n ≤ m) : EvalsToInTime f a b m :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hn⟩

/-- Restoration moves one bit per transition and actually empties scratch. -/
def successor_restore (v) (xs ys : List Bool) :
    EvalsToInTime successorMachine.step (succCfg (some true) v xs ys)
      (some (succCfg none none (ys.reverse ++ xs) [])) (ys.length + 1) := by
  induction ys generalizing xs v with
  | nil => simpa using oneStep successorMachine.step (successor_step_restore_nil v xs)
  | cons b ys ih =>
      have h := EvalsToInTime.trans successorMachine.step 1 (ys.length + 1) _ _ _
        (oneStep successorMachine.step (successor_step_restore_cons v b xs ys))
        (ih (some b) (b :: xs))
      simpa [List.reverse_cons, List.append_assoc] using h

/-- Carry propagation and scratch restoration, with a linear bit-cost bound. -/
def successor_run (v) (xs ys : List Bool) :
    EvalsToInTime successorMachine.step (succCfg (some false) v xs ys)
      (some (succCfg none none (ys.reverse ++ succBits xs) []))
      (2 * xs.length + ys.length + 2) := by
  induction xs generalizing v ys with
  | nil =>
      have h := EvalsToInTime.trans successorMachine.step 1 (ys.length + 1) _ _ _
        (oneStep successorMachine.step (successor_step_carry_nil v ys))
        (successor_restore none [true] ys)
      simpa [succBits] using h
  | cons b xs ih =>
      cases b with
      | false =>
          have h := EvalsToInTime.trans successorMachine.step 1 (ys.length + 1) _ _ _
            (oneStep successorMachine.step (successor_step_carry_false v xs ys))
            (successor_restore (some false) (true :: xs) ys)
          apply weakenTime (by simpa [succBits] using h)
          simp
      | true =>
          have h := EvalsToInTime.trans successorMachine.step 1
            (2 * xs.length + (false :: ys).length + 2) _ _ _
            (oneStep successorMachine.step (successor_step_carry_true v xs ys))
            (ih (some true) (false :: ys))
          have ht : (2 * xs.length + (false :: ys).length + 2) + 1 =
              2 * (true :: xs).length + ys.length + 2 := by simp; omega
          rw [ht] at h
          simpa [succBits, List.reverse_cons, List.append_assoc] using h

/-- The machine's concrete input/output configurations match mathlib's strict
output convention: no garbage stacks or stale finite-control registers. -/
def successor_outputs (xs : List Bool) :
    TM2OutputsInTime successorMachine xs (some (succBits xs)) (2 * xs.length + 2) := by
  have h := successor_run none xs []
  have hi : initList successorMachine xs = succCfg (some false) none xs [] := by
    unfold initList succCfg
    congr 1
    funext k; cases k <;> rfl
  have ho : haltList successorMachine (succBits xs) = succCfg none none (succBits xs) [] := by
    unfold haltList succCfg
    congr 1
    funext k; cases k <;> rfl
  simpa [TM2OutputsInTime, hi, ho] using h

/-- A fully instantiated polynomial-time TM2 computation on the project's
binary natural-number encoding. -/
noncomputable def successorComputable :
    TM2ComputableInPolyTime Complexity.BitEncoding.nat.toFinEncoding
      Complexity.BitEncoding.nat.toFinEncoding (fun n => n + 1) where
  tm := successorMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun n := by
    simpa [Complexity.BitEncoding.nat, Complexity.BitEncoding.toFinEncoding,
      Polynomial.eval_add, Polynomial.eval_mul, Equiv.refl, Equiv.symm] using
      successor_outputs (Computability.encodeNat n)

theorem fp_successor :
    Complexity.FP Complexity.BitEncoding.nat Complexity.BitEncoding.nat (fun n => n + 1) :=
  ⟨successorComputable⟩

end PlanarHom.BinaryArithmetic
