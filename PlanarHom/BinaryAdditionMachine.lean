import PlanarHom.BinaryAdditionBits

/-!
# A finite-control binary addition machine

The input has the exact framed product encoding from `Complexity`. Parsing,
reversal, carry arithmetic, and output cleanup are all ordinary TM2 statements.
-/

namespace PlanarHom.BinaryArithmetic

open Turing Turing.TM2

abbrev AddState := Bool × Option Bool × Option Bool

/-- Three bit stacks: input/output, scratch, and the first summand. -/
def additionMachine : FinTM2 where
  K := Option Bool
  k₀ := none
  k₁ := none
  Γ _ := Bool
  Λ := Bool × Bool
  main := (false, false)
  σ := AddState
  initialState := (false, none, none)
  m
    | (false, false) =>
        .pop none (fun v b => (v.1, b, v.2.2)) <|
          .branch (fun v => v.2.1.getD false)
            (.pop none (fun v b => (v.1, b, v.2.2)) <|
              .push (some false) (fun v => v.2.1.getD false) <|
                .goto (fun _ => (false, false)))
            (.goto (fun _ => (false, true)))
    | (false, true) =>
        .pop (some false) (fun v b => (v.1, b, v.2.2)) <|
          .branch (fun v => v.2.1.isSome)
            (.push (some true) (fun v => v.2.1.getD false) <|
              .goto (fun _ => (false, true)))
            (.load (fun _ => (false, none, none)) <|
              .goto (fun _ => (true, false)))
    | (true, false) =>
        .pop (some true) (fun v b => (v.1, b, v.2.2)) <|
          .pop none (fun v b => (v.1, v.2.1, b)) <|
            .branch (fun v => v.2.1.isSome || v.2.2.isSome)
              (.push (some false)
                (fun v => xor (xor (v.2.1.getD false) (v.2.2.getD false)) v.1) <|
                .load (fun v =>
                  (((v.2.1.getD false && v.2.2.getD false) ||
                    (v.2.1.getD false && v.1) || (v.2.2.getD false && v.1)),
                    none, none)) <|
                  .goto (fun _ => (true, false)))
              (.branch (fun v => v.1)
                (.push (some false) (fun _ => true) <| .goto (fun _ => (true, true)))
                (.goto (fun _ => (true, true))))
    | (true, true) =>
        .pop (some false) (fun v b => (v.1, b, v.2.2)) <|
          .branch (fun v => v.2.1.isSome)
            (.push none (fun v => v.2.1.getD false) <|
              .goto (fun _ => (true, true)))
            (.load (fun _ => (false, none, none)) .halt)

def addCfg (label : Option (Bool × Bool)) (v : AddState) (xs ys zs : List Bool) :
    additionMachine.Cfg :=
  ⟨label, v, fun k : Option Bool => match k with
    | none => xs
    | some false => ys
    | some true => zs⟩

@[simp] theorem addition_step_parse_bit (v : AddState) (b : Bool) (xs ys zs : List Bool) :
    additionMachine.step (addCfg (some (false, false)) v (true :: b :: xs) ys zs) =
      some (addCfg (some (false, false)) (v.1, some b, v.2.2) xs (b :: ys) zs) := by
  simp [additionMachine, addCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem addition_step_parse_end (v : AddState) (xs ys zs : List Bool) :
    additionMachine.step (addCfg (some (false, false)) v (false :: xs) ys zs) =
      some (addCfg (some (false, true)) (v.1, some false, v.2.2) xs ys zs) := by
  simp [additionMachine, addCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem addition_step_reverse_cons (v : AddState) (b : Bool) (xs ys zs : List Bool) :
    additionMachine.step (addCfg (some (false, true)) v xs (b :: ys) zs) =
      some (addCfg (some (false, true)) (v.1, some b, v.2.2) xs ys (b :: zs)) := by
  simp [additionMachine, addCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem addition_step_reverse_nil (v : AddState) (xs zs : List Bool) :
    additionMachine.step (addCfg (some (false, true)) v xs [] zs) =
      some (addCfg (some (true, false)) (false, none, none) xs [] zs) := by
  simp [additionMachine, addCfg, step, stepAux]

@[simp] theorem addition_step_restore_cons (v : AddState) (b : Bool) (xs ys : List Bool) :
    additionMachine.step (addCfg (some (true, true)) v xs (b :: ys) []) =
      some (addCfg (some (true, true)) (v.1, some b, v.2.2) (b :: xs) ys []) := by
  simp [additionMachine, addCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem addition_step_restore_nil (v : AddState) (xs : List Bool) :
    additionMachine.step (addCfg (some (true, true)) v xs [] []) =
      some (addCfg none (false, none, none) xs [] []) := by
  simp [additionMachine, addCfg, step, stepAux]

/-- Output reversal restores the initial finite-control state and empties scratch. -/
def addition_restore (v : AddState) (xs ys : List Bool) :
    EvalsToInTime additionMachine.step (addCfg (some (true, true)) v xs ys [])
      (some (addCfg none (false, none, none) (ys.reverse ++ xs) [] []))
      (ys.length + 1) := by
  induction ys generalizing xs v with
  | nil => simpa using oneStep additionMachine.step (addition_step_restore_nil v xs)
  | cons b ys ih =>
      have h := EvalsToInTime.trans additionMachine.step 1 (ys.length + 1) _ _ _
        (oneStep additionMachine.step (addition_step_restore_cons v b xs ys))
        (ih (v.1, some b, v.2.2) (b :: xs))
      simpa [List.reverse_cons, List.append_assoc] using h

/-- Reading the framed first word consumes its actual bits and delimiter. -/
def addition_parse (v : AddState) (xs ys zs ws : List Bool) :
    EvalsToInTime additionMachine.step
      (addCfg (some (false, false)) v (Complexity.BitEncoding.frame xs ++ ys) zs ws)
      (some (addCfg (some (false, true)) (v.1, some false, v.2.2)
        ys (xs.reverse ++ zs) ws)) (xs.length + 1) := by
  induction xs generalizing v zs with
  | nil => simpa [Complexity.BitEncoding.frame] using
      oneStep additionMachine.step (addition_step_parse_end v ys zs ws)
  | cons b xs ih =>
      have h := EvalsToInTime.trans additionMachine.step 1 (xs.length + 1) _ _ _
        (oneStep additionMachine.step
          (addition_step_parse_bit v b (Complexity.BitEncoding.frame xs ++ ys) zs ws))
        (ih (v.1, some b, v.2.2) (b :: zs))
      simpa [Complexity.BitEncoding.frame, List.reverse_cons, List.append_assoc] using h

/-- Reversing the parsed word puts both summands least-significant-bit first. -/
def addition_reverse (v : AddState) (xs ys zs : List Bool) :
    EvalsToInTime additionMachine.step (addCfg (some (false, true)) v xs ys zs)
      (some (addCfg (some (true, false)) (false, none, none)
        xs [] (ys.reverse ++ zs))) (ys.length + 1) := by
  induction ys generalizing zs v with
  | nil => simpa using oneStep additionMachine.step (addition_step_reverse_nil v xs zs)
  | cons b ys ih =>
      have h := EvalsToInTime.trans additionMachine.step 1 (ys.length + 1) _ _ _
        (oneStep additionMachine.step (addition_step_reverse_cons v b xs ys zs))
        (ih (v.1, some b, v.2.2) (b :: zs))
      simpa [List.reverse_cons, List.append_assoc] using h


@[simp] theorem addition_step_finish (v : AddState) (zs : List Bool) :
    additionMachine.step (addCfg (some (true, false)) v [] zs []) =
      some (addCfg (some (true, true)) (v.1, none, none) []
        (if v.1 then true :: zs else zs) []) := by
  rcases v with ⟨c, a, b⟩
  cases c <;> simp [additionMachine, addCfg, step, stepAux]
  all_goals funext k; rcases k with _ | (_ | _) <;> simp

/-- One full-adder transition consumes at most one bit from each input stack. -/
theorem addition_step_add (v : AddState) (xs ys zs : List Bool)
    (h : xs ≠ [] ∨ ys ≠ []) :
    additionMachine.step (addCfg (some (true, false)) v ys zs xs) =
      some (addCfg (some (true, false))
        (((xs.head?.getD false && ys.head?.getD false) ||
          (xs.head?.getD false && v.1) || (ys.head?.getD false && v.1)), none, none)
        ys.tail ((xor (xor (xs.head?.getD false) (ys.head?.getD false)) v.1) :: zs)
        xs.tail) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp [additionMachine, addCfg, step, stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp
  | cons x xs =>
    cases ys with
    | nil =>
      simp [additionMachine, addCfg, step, stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp
    | cons y ys =>
      simp [additionMachine, addCfg, step, stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp


private theorem addBits_step (c : Bool) (xs ys : List Bool) (h : xs ≠ [] ∨ ys ≠ []) :
    addBits c xs ys =
      fullAdderBit (xs.head?.getD false) (ys.head?.getD false) c ::
        addBits (fullAdderCarry (xs.head?.getD false) (ys.head?.getD false) c)
          xs.tail ys.tail := by
  cases xs <;> cases ys <;> simp_all only [addBits, List.head?_nil, List.head?_cons,
    Option.getD_none, Option.getD_some, List.tail_nil, List.tail_cons, ne_eq, not_true_eq_false,
    or_self]

/-- Arithmetic plus final reversal takes linear time even on noncanonical bit
strings; the accumulator is returned in order and all workspace is empty. -/
def addition_run (v : AddState) (xs ys zs : List Bool) :
    EvalsToInTime additionMachine.step (addCfg (some (true, false)) v ys zs xs)
      (some (addCfg none (false, none, none) (zs.reverse ++ addBits v.1 xs ys) [] []))
      (2 * (xs.length + ys.length) + zs.length + 3) := by
  by_cases h : xs = [] ∧ ys = []
  · rcases h with ⟨rfl, rfl⟩
    rcases v with ⟨c, a, b⟩
    cases c with
    | false =>
      have he := EvalsToInTime.trans additionMachine.step 1 (zs.length + 1) _ _ _
        (oneStep additionMachine.step (addition_step_finish (false, a, b) zs))
        (addition_restore (false, none, none) [] zs)
      apply weakenTime (by simpa [addBits] using he)
      simp
    | true =>
      have he := EvalsToInTime.trans additionMachine.step 1 ((true :: zs).length + 1) _ _ _
        (oneStep additionMachine.step (addition_step_finish (true, a, b) zs))
        (addition_restore (true, none, none) [] (true :: zs))
      simpa [addBits, List.reverse_cons, Nat.add_assoc] using he
  · have hn : xs ≠ [] ∨ ys ≠ [] := by tauto
    let bit := fullAdderBit (xs.head?.getD false) (ys.head?.getD false) v.1
    let carry := fullAdderCarry (xs.head?.getD false) (ys.head?.getD false) v.1
    have hs : additionMachine.step (addCfg (some (true, false)) v ys zs xs) =
        some (addCfg (some (true, false)) (carry, none, none) ys.tail (bit :: zs) xs.tail) := by
      simpa [bit, carry, fullAdderBit, fullAdderCarry] using addition_step_add v xs ys zs hn
    have he := EvalsToInTime.trans additionMachine.step 1
      (2 * (xs.tail.length + ys.tail.length) + (bit :: zs).length + 3) _ _ _
      (oneStep additionMachine.step hs)
      (addition_run (carry, none, none) xs.tail ys.tail (bit :: zs))
    have hout : (bit :: zs).reverse ++ addBits carry xs.tail ys.tail =
        zs.reverse ++ addBits v.1 xs ys := by
      rw [addBits_step v.1 xs ys hn]
      simp [bit, carry, List.reverse_cons, List.append_assoc]
    rw [hout] at he
    apply weakenTime he
    have hl : xs.tail.length + ys.tail.length + 1 ≤ xs.length + ys.length := by
      cases xs <;> cases ys <;> simp_all
      omega
    simp only [List.length_cons]
    omega
termination_by xs.length + ys.length
decreasing_by
  have hn : xs ≠ [] ∨ ys ≠ [] := by tauto
  cases xs <;> cases ys <;> simp_all
  omega

/-- The framed two-word input is parsed and added in at most `4|x| + 2|y| + 5`
actual machine transitions, including input parsing and output cleanup. -/
def addition_outputs (xs ys : List Bool) :
    TM2OutputsInTime additionMachine (Complexity.BitEncoding.frame xs ++ ys)
      (some (addBits false xs ys)) (4 * xs.length + 2 * ys.length + 5) := by
  have hp := addition_parse (false, none, none) xs ys [] []
  have hr := addition_reverse (false, some false, none) ys xs.reverse []
  have ha := addition_run (false, none, none) xs ys []
  simp only [List.append_nil, List.reverse_nil, List.nil_append, List.length_nil,
    Nat.add_zero, List.reverse_reverse, List.length_reverse] at hp hr ha
  have hpr := EvalsToInTime.trans additionMachine.step (xs.length + 1) (xs.length + 1)
    _ _ _ hp hr
  have hall := EvalsToInTime.trans additionMachine.step ((xs.length + 1) + (xs.length + 1))
    (2 * (xs.length + ys.length) + 3) _ _ _ hpr ha
  have hi : initList additionMachine (Complexity.BitEncoding.frame xs ++ ys) =
      addCfg (some (false, false)) (false, none, none)
        (Complexity.BitEncoding.frame xs ++ ys) [] [] := by
    unfold initList addCfg
    congr 1
    funext k; rcases k with _ | (_ | _) <;> rfl
  have ho : haltList additionMachine (addBits false xs ys) =
      addCfg none (false, none, none) (addBits false xs ys) [] [] := by
    unfold haltList addCfg
    congr 1
    funext k; rcases k with _ | (_ | _) <;> rfl
  have ht : (2 * (xs.length + ys.length) + 3) + ((xs.length + 1) + (xs.length + 1)) =
      4 * xs.length + 2 * ys.length + 5 := by omega
  rw [ht] at hall
  simpa [TM2OutputsInTime, hi, ho] using hall

/-- Addition under the project's exact framed binary product encoding has a
linear, hence polynomial, time bound `2 * input bit-length + 3`. -/
noncomputable def additionComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat).toFinEncoding
      Complexity.BitEncoding.nat.toFinEncoding (fun n : ℕ × ℕ => n.1 + n.2) where
  tm := additionMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun n := by
    have h := addition_outputs (Computability.encodeNat n.1) (Computability.encodeNat n.2)
    have ht : 4 * (Computability.encodeNat n.1).length +
        2 * (Computability.encodeNat n.2).length + 5 =
        2 * (2 * (Computability.encodeNat n.1).length +
          (Computability.encodeNat n.2).length + 1) + 3 := by omega
    rw [ht] at h
    simpa [Complexity.BitEncoding.nat, Complexity.BitEncoding.prod,
      Complexity.BitEncoding.toFinEncoding, Complexity.BitEncoding.frame_length,
      Polynomial.eval_add, Polynomial.eval_mul, Equiv.refl, Equiv.symm,
      addBits_encodeNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem fp_addition :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat)
      Complexity.BitEncoding.nat (fun n : ℕ × ℕ => n.1 + n.2) :=
  ⟨additionComputable⟩

end PlanarHom.BinaryArithmetic
