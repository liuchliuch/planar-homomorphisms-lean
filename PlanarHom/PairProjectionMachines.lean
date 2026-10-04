import PlanarHom.Complexity
import PlanarHom.StackTransfer
import Mathlib.Tactic.DeriveFintype

/-!
# Genuine machines for framed-pair projections and concatenation

The input is literally `frame a ++ b`. A finite parser consumes one framing
marker and one data bit per iteration. Two Boolean stacks suffice, and every
successful output has the exact `haltList` convention, including empty scratch
storage and restored finite control.
-/

namespace PlanarHom.Complexity.PairProjectionMachines

open Turing Turing.TM2 PlanarHom.MachineComposition

noncomputable section

inductive Label | parse | clear | restore | halt
  deriving DecidableEq, Fintype

abbrev State := Unit × Option Bool
abbrev Alphabet (_ : Bool) := Bool

/-- The input/output stack and the reversed-prefix scratch stack. -/
def store (input scratch : Bits) : Bool → Bits
  | false => input
  | true => scratch

@[simp] theorem store_false (input scratch : Bits) : store input scratch false = input := rfl
@[simp] theorem store_true (input scratch : Bits) : store input scratch true = scratch := rfl

@[simp] theorem store_update_false (input scratch value : Bits) :
    Function.update (store input scratch) false value = store value scratch := by
  funext k
  cases k <;> simp [store]

@[simp] theorem store_update_true (input scratch value : Bits) :
    Function.update (store input scratch) true value = store input value := by
  funext k
  cases k <;> simp [store]

def config (label : Option Label) (input scratch : Bits) : Cfg Alphabet Label State :=
  ⟨label, ((), none), store input scratch⟩

def parseNext (keepPrefix keepSuffix : Bool) : Label :=
  if keepSuffix then (if keepPrefix then .restore else .halt) else .clear

/-- Parse one frame symbol. Every branch is finite actual TM2 syntax. -/
def parseStmt (keepPrefix : Bool) (next : Label) : Stmt Alphabet Label State :=
  .pop false (fun _ a => ((), a))
    (.branch (fun v => v.2.getD false)
      (.pop false (fun _ a => ((), a))
        (if keepPrefix then
          .push true (fun v => v.2.getD false)
            (.load (fun _ => ((), none)) (.goto (fun _ => .parse)))
        else .load (fun _ => ((), none)) (.goto (fun _ => .parse))))
      (.load (fun _ => ((), none)) (.goto (fun _ => next))))

/-- A common finite program for both projections and concatenation. -/
def program (keepPrefix keepSuffix : Bool) : Label → Stmt Alphabet Label State
  | .parse => parseStmt keepPrefix (parseNext keepPrefix keepSuffix)
  | .clear => clearStmt false .clear .restore
  | .restore => transferStmt true false id id .restore .halt
  | .halt => .halt

def pairMachine (keepPrefix keepSuffix : Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ := Alphabet
  Λ := Label
  main := .parse
  σ := State
  initialState := ((), none)
  m := program keepPrefix keepSuffix

abbrev iter (keepPrefix keepSuffix : Bool) (n : ℕ) :=
  (fun c : Option (Cfg Alphabet Label State) => c.bind (step (program keepPrefix keepSuffix)))^[n]

theorem iter_add (kp ks : Bool) (n t : ℕ) (c : Option (Cfg Alphabet Label State)) :
    iter kp ks (n + t) c = iter kp ks n (iter kp ks t c) :=
  Function.iterate_add_apply _ _ _ _

theorem iter_succ (kp ks : Bool) (n : ℕ) (c : Option (Cfg Alphabet Label State)) :
    iter kp ks (n + 1) c = iter kp ks n (c.bind (step (program kp ks))) :=
  Function.iterate_succ_apply _ _ _

@[simp] theorem parse_nil (kp ks : Bool) (b acc : Bits) :
    step (program kp ks) (config (some .parse) (BitEncoding.frame [] ++ b) acc) =
      some (config (some (parseNext kp ks)) b acc) := by
  simp [program, parseStmt, BitEncoding.frame, config]

@[simp] theorem parse_cons (kp ks a : Bool) (as b acc : Bits) :
    step (program kp ks) (config (some .parse) (BitEncoding.frame (a :: as) ++ b) acc) =
      some (config (some .parse) (BitEncoding.frame as ++ b) (if kp then a :: acc else acc)) := by
  cases kp <;> simp [program, parseStmt, BitEncoding.frame, config]

/-- The framed prefix is parsed in exactly one transition per bit plus its end marker. -/
theorem parse_run (kp ks : Bool) (a b acc : Bits) :
    iter kp ks (a.length + 1)
      (some (config (some .parse) (BitEncoding.frame a ++ b) acc)) =
      some (config (some (parseNext kp ks)) b (if kp then a.reverse ++ acc else acc)) := by
  induction a generalizing acc with
  | nil => simp [iter]
  | cons a as ih =>
      rw [List.length_cons, iter_succ]
      change iter kp ks (as.length + 1)
        (step (program kp ks) (config (some .parse) (BitEncoding.frame (a :: as) ++ b) acc)) = _
      rw [parse_cons, ih]
      cases kp <;> simp [List.reverse_cons, List.append_assoc]

/-- Clearing the suffix is a genuine bounded loop. -/
theorem clear_run (kp ks : Bool) (input scratch : Bits) :
    iter kp ks (input.length + 1) (some (config (some .clear) input scratch)) =
      some (config (some .restore) [] scratch) := by
  have h := MachineComposition.clear_run (program kp ks) false .clear .restore rfl
    () none (store input scratch)
  simpa [iter, config] using h

/-- Restore the reversed prefix onto the desired suffix. -/
theorem restore_run (kp ks : Bool) (input scratch : Bits) :
    iter kp ks (scratch.length + 1) (some (config (some .restore) input scratch)) =
      some (config (some .halt) (scratch.reverse ++ input) []) := by
  have h := transfer_run (program kp ks) true false (by decide) id id .restore .halt rfl
    () none (store input scratch)
  simpa [iter, config, transferStore, Function.comp_def] using h

@[simp] theorem halt_step (kp ks : Bool) (output : Bits) :
    iter kp ks 1 (some (config (some .halt) output [])) =
      some (config none output []) := by
  simp [iter, config, program]

@[simp] theorem initial_config (kp ks : Bool) (input : Bits) :
    initList (pairMachine kp ks) input = config (some .parse) input [] := by
  apply congrArg (fun S : Bool → Bits =>
    (⟨some Label.parse, ((), none), S⟩ : Cfg Alphabet Label State))
  funext k
  cases k <;> simp [pairMachine, store]

@[simp] theorem final_config (kp ks : Bool) (output : Bits) :
    haltList (pairMachine kp ks) output = config none output [] := by
  apply congrArg (fun S : Bool → Bits =>
    (⟨none, ((), none), S⟩ : Cfg Alphabet Label State))
  funext k
  cases k <;> simp [pairMachine, store]

/-- Exact first-projection execution, with every unused stack empty at termination. -/
theorem fst_run (a b : Bits) :
    iter true false (2 * a.length + b.length + 4)
      (some (config (some .parse) (BitEncoding.frame a ++ b) [])) =
      some (config none a []) := by
  have hp := parse_run true false a b []
  have hc := clear_run true false b a.reverse
  have hr := restore_run true false [] a.reverse
  simp only [List.append_nil] at hp
  change iter true false (a.length + 1)
    (some (config (some .parse) (BitEncoding.frame a ++ b) [])) =
    some (config (some .clear) b a.reverse) at hp
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hn : 2 * a.length + b.length + 4 = 1 + ((a.length + 1) + ((b.length + 1) + (a.length + 1))) := by omega
  rw [hn, iter_add _ _ 1, iter_add _ _ (a.length + 1),
    iter_add _ _ (b.length + 1), hp, hc, hr, halt_step]

/-- Exact second-projection execution. -/
theorem snd_run (a b : Bits) :
    iter false true (a.length + 2)
      (some (config (some .parse) (BitEncoding.frame a ++ b) [])) =
      some (config none b []) := by
  have hp := parse_run false true a b []
  change iter false true (a.length + 1)
    (some (config (some .parse) (BitEncoding.frame a ++ b) [])) =
    some (config (some .halt) b []) at hp
  have hn : a.length + 2 = 1 + (a.length + 1) := by omega
  rw [hn, iter_add _ _ 1, hp, halt_step]

/-- Exact concatenation execution. -/
theorem append_run (a b : Bits) :
    iter true true (2 * a.length + 3)
      (some (config (some .parse) (BitEncoding.frame a ++ b) [])) =
      some (config none (a ++ b) []) := by
  have hp := parse_run true true a b []
  have hr := restore_run true true b a.reverse
  simp only [List.append_nil] at hp
  change iter true true (a.length + 1)
    (some (config (some .parse) (BitEncoding.frame a ++ b) [])) =
    some (config (some .restore) b a.reverse) at hp
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have hn : 2 * a.length + 3 = 1 + ((a.length + 1) + (a.length + 1)) := by omega
  rw [hn, iter_add _ _ 1, iter_add _ _ (a.length + 1), hp, hr, halt_step]

/-- The first projection obeys the exact input/output convention in linear time. -/
def fst_outputs (a b : Bits) :
    TM2OutputsInTime (pairMachine true false) (BitEncoding.frame a ++ b) (some a)
      ((BitEncoding.frame a ++ b).length + 3) where
  steps := 2 * a.length + b.length + 4
  evals_in_steps := by
    change iter true false (2 * a.length + b.length + 4)
      (some (initList (pairMachine true false) (BitEncoding.frame a ++ b))) =
      some (haltList (pairMachine true false) a)
    rw [initial_config, final_config]
    exact fst_run a b
  steps_le_m := by simp [BitEncoding.frame_length]; omega

/-- The second projection discards framing and prefix bits in linear time. -/
def snd_outputs (a b : Bits) :
    TM2OutputsInTime (pairMachine false true) (BitEncoding.frame a ++ b) (some b)
      ((BitEncoding.frame a ++ b).length + 3) where
  steps := a.length + 2
  evals_in_steps := by
    change iter false true (a.length + 2)
      (some (initList (pairMachine false true) (BitEncoding.frame a ++ b))) =
      some (haltList (pairMachine false true) b)
    rw [initial_config, final_config]
    exact snd_run a b
  steps_le_m := by simp [BitEncoding.frame_length]; omega

/-- Concatenation restores the parsed prefix onto the unframed suffix. -/
def append_outputs (a b : Bits) :
    TM2OutputsInTime (pairMachine true true) (BitEncoding.frame a ++ b) (some (a ++ b))
      ((BitEncoding.frame a ++ b).length + 3) where
  steps := 2 * a.length + 3
  evals_in_steps := by
    change iter true true (2 * a.length + 3)
      (some (initList (pairMachine true true) (BitEncoding.frame a ++ b))) =
      some (haltList (pairMachine true true) (a ++ b))
    rw [initial_config, final_config]
    exact append_run a b
  steps_le_m := by simp [BitEncoding.frame_length]; omega

/-- First projection for arbitrary binary component encodings: the machine
extracts the existing codeword without computing either encoding. -/
def fstEncodingComputer {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) :
    TM2ComputableInPolyTime (ea.prod eb).toFinEncoding ea.toFinEncoding
      (Prod.fst : α × β → α) where
  tm := pairMachine true false
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + Polynomial.C 3
  outputsFun x := by
    simpa [Equiv.refl, BitEncoding.toFinEncoding, BitEncoding.prod, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C] using fst_outputs (ea.encode x.1) (eb.encode x.2)

/-- Second projection for arbitrary binary component encodings. -/
def sndEncodingComputer {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) :
    TM2ComputableInPolyTime (ea.prod eb).toFinEncoding eb.toFinEncoding
      (Prod.snd : α × β → β) where
  tm := pairMachine false true
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + Polynomial.C 3
  outputsFun x := by
    simpa [Equiv.refl, BitEncoding.toFinEncoding, BitEncoding.prod, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C] using snd_outputs (ea.encode x.1) (eb.encode x.2)

/-- Bit-pair first projection, using literal framed concatenation as input. -/
def fstComputer := fstEncodingComputer BitEncoding.bits BitEncoding.bits

/-- Bit-pair second projection. -/
def sndComputer := sndEncodingComputer BitEncoding.bits BitEncoding.bits

/-- Bit-string concatenation from a literally framed input pair. -/
def appendComputer :
    TM2ComputableInPolyTime (BitEncoding.bits.prod BitEncoding.bits).toFinEncoding
      BitEncoding.bits.toFinEncoding (fun x : Bits × Bits => x.1 ++ x.2) where
  tm := pairMachine true true
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + Polynomial.C 3
  outputsFun x := by
    simpa [Equiv.refl, BitEncoding.toFinEncoding, BitEncoding.prod, BitEncoding.bits, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C] using append_outputs x.1 x.2

theorem fp_fst {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) :
    FP (ea.prod eb) ea (Prod.fst : α × β → α) := ⟨fstEncodingComputer ea eb⟩

theorem fp_snd {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) :
    FP (ea.prod eb) eb (Prod.snd : α × β → β) := ⟨sndEncodingComputer ea eb⟩

theorem fp_append : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bits
    (fun x : Bits × Bits => x.1 ++ x.2) := ⟨appendComputer⟩

end

end PlanarHom.Complexity.PairProjectionMachines
