import PlanarHom.BinaryMultiplicationBits
import PlanarHom.BinaryAdditionMachine

/-!
# A binary shift-add multiplication TM2

A fixed five-stack, eight-label finite-control machine. The multiplicand is
preserved by the full adder, and every shift preserves canonical zero.
-/

namespace PlanarHom.BinaryArithmetic

open Turing Turing.TM2

inductive MulStack | input | x | z | sx | sz deriving DecidableEq, Fintype
inductive MulLabel | parse | reverseInput | loop | add | restoreX | restoreZ | shift | clear
  deriving DecidableEq, Fintype

/-- All arithmetic takes place in finite-control Boolean gates and individual
stack push/pop instructions. -/
def multiplicationMachine : FinTM2 where
  K := MulStack
  k₀ := .input
  k₁ := .z
  Γ _ := Bool
  Λ := MulLabel
  main := .parse
  σ := AddState
  initialState := (false, none, none)
  m
    | .parse => .pop .input (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.getD false)
          (.pop .input (fun v b => (v.1, b, v.2.2)) <|
            .push .sx (fun v => v.2.1.getD false) (.goto (fun _ => .parse)))
          (.goto (fun _ => .reverseInput))
    | .reverseInput => .pop .sx (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push .x (fun v => v.2.1.getD false) (.goto (fun _ => .reverseInput)))
          (.load (fun _ => (false, none, none)) (.goto (fun _ => .loop)))
    | .loop => .pop .input (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.branch (fun v => v.2.1.getD false)
            (.load (fun _ => (false, none, none)) (.goto (fun _ => .add)))
            (.goto (fun _ => .shift)))
          (.goto (fun _ => .clear))
    | .add =>
      let next : Stmt (fun _ : MulStack => Bool) MulLabel AddState :=
        .branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (.push .sz (fun v => fullAdderBit (v.2.1.getD false) (v.2.2.getD false) v.1) <|
            .load (fun v => (fullAdderCarry (v.2.1.getD false) (v.2.2.getD false) v.1,
              none, none)) (.goto (fun _ => .add)))
          (.branch (fun v => v.1)
            (.push .sz (fun _ => true) (.goto (fun _ => .restoreX)))
            (.goto (fun _ => .restoreX)))
      .pop .x (fun v b => (v.1, b, v.2.2)) <|
        .pop .z (fun v b => (v.1, v.2.1, b)) <|
          .branch (fun v => v.2.1.isSome)
            (.push .sx (fun v => v.2.1.getD false) next) next
    | .restoreX => .pop .sx (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push .x (fun v => v.2.1.getD false) (.goto (fun _ => .restoreX)))
          (.goto (fun _ => .restoreZ))
    | .restoreZ => .pop .sz (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push .z (fun v => v.2.1.getD false) (.goto (fun _ => .restoreZ)))
          (.load (fun _ => (false, none, none)) (.goto (fun _ => .shift)))
    | .shift => .peek .x (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push .x (fun _ => false) <|
            .load (fun _ => (false, none, none)) (.goto (fun _ => .loop)))
          (.load (fun _ => (false, none, none)) (.goto (fun _ => .loop)))
    | .clear => .pop .x (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.goto (fun _ => .clear))
          (.load (fun _ => (false, none, none)) .halt)

/-- Expose every stack of the concrete machine. -/
def mulCfg (label : Option MulLabel) (v : AddState) (ms xs zs as bs : List Bool) :
    multiplicationMachine.Cfg :=
  ⟨label, v, fun k : MulStack => match k with
    | .input => ms | .x => xs | .z => zs | .sx => as | .sz => bs⟩

@[simp] theorem multiplication_step_parse_bit (v : AddState) (b : Bool)
    (ms xs zs as bs : List Bool) :
    multiplicationMachine.step (mulCfg (some .parse) v (true :: b :: ms) xs zs as bs) =
      some (mulCfg (some .parse) (v.1, some b, v.2.2) ms xs zs (b :: as) bs) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem multiplication_step_parse_end (v : AddState) (ms xs zs as bs : List Bool) :
    multiplicationMachine.step (mulCfg (some .parse) v (false :: ms) xs zs as bs) =
      some (mulCfg (some .reverseInput) (v.1, some false, v.2.2) ms xs zs as bs) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem multiplication_step_reverse_cons (v : AddState) (b : Bool)
    (ms xs zs as bs : List Bool) :
    multiplicationMachine.step (mulCfg (some .reverseInput) v ms xs zs (b :: as) bs) =
      some (mulCfg (some .reverseInput) (v.1, some b, v.2.2) ms (b :: xs) zs as bs) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem multiplication_step_reverse_nil (v : AddState) (ms xs zs bs : List Bool) :
    multiplicationMachine.step (mulCfg (some .reverseInput) v ms xs zs [] bs) =
      some (mulCfg (some .loop) (false, none, none) ms xs zs [] bs) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]

@[simp] theorem multiplication_step_loop_false (v : AddState) (ms xs zs : List Bool) :
    multiplicationMachine.step (mulCfg (some .loop) v (false :: ms) xs zs [] []) =
      some (mulCfg (some .shift) (v.1, some false, v.2.2) ms xs zs [] []) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem multiplication_step_loop_true (v : AddState) (ms xs zs : List Bool) :
    multiplicationMachine.step (mulCfg (some .loop) v (true :: ms) xs zs [] []) =
      some (mulCfg (some .add) (false, none, none) ms xs zs [] []) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem multiplication_step_loop_nil (v : AddState) (xs zs : List Bool) :
    multiplicationMachine.step (mulCfg (some .loop) v [] xs zs [] []) =
      some (mulCfg (some .clear) (v.1, none, v.2.2) [] xs zs [] []) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]

@[simp] theorem multiplication_step_shift (v : AddState) (ms xs zs : List Bool) :
    multiplicationMachine.step (mulCfg (some .shift) v ms xs zs [] []) =
      some (mulCfg (some .loop) (false, none, none) ms (shiftBits xs) zs [] []) := by
  cases xs with
  | nil => simp [multiplicationMachine, mulCfg, step, stepAux]
  | cons b xs =>
    simp [multiplicationMachine, mulCfg, step, stepAux]
    funext k; cases k <;> simp

@[simp] theorem multiplication_step_clear_cons (v : AddState) (b : Bool) (xs zs : List Bool) :
    multiplicationMachine.step (mulCfg (some .clear) v [] (b :: xs) zs [] []) =
      some (mulCfg (some .clear) (v.1, some b, v.2.2) [] xs zs [] []) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem multiplication_step_clear_nil (v : AddState) (zs : List Bool) :
    multiplicationMachine.step (mulCfg (some .clear) v [] [] zs [] []) =
      some (mulCfg none (false, none, none) [] [] zs [] []) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]

@[simp] theorem multiplication_step_restoreX_cons (v : AddState) (b : Bool)
    (ms xs zs as bs : List Bool) :
    multiplicationMachine.step (mulCfg (some .restoreX) v ms xs zs (b :: as) bs) =
      some (mulCfg (some .restoreX) (v.1, some b, v.2.2) ms (b :: xs) zs as bs) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem multiplication_step_restoreX_nil (v : AddState) (ms xs zs bs : List Bool) :
    multiplicationMachine.step (mulCfg (some .restoreX) v ms xs zs [] bs) =
      some (mulCfg (some .restoreZ) (v.1, none, v.2.2) ms xs zs [] bs) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]

@[simp] theorem multiplication_step_restoreZ_cons (v : AddState) (b : Bool)
    (ms xs zs bs : List Bool) :
    multiplicationMachine.step (mulCfg (some .restoreZ) v ms xs zs [] (b :: bs)) =
      some (mulCfg (some .restoreZ) (v.1, some b, v.2.2) ms xs (b :: zs) [] bs) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]
  funext k; cases k <;> simp

@[simp] theorem multiplication_step_restoreZ_nil (v : AddState) (ms xs zs : List Bool) :
    multiplicationMachine.step (mulCfg (some .restoreZ) v ms xs zs [] []) =
      some (mulCfg (some .shift) (false, none, none) ms xs zs [] []) := by
  simp [multiplicationMachine, mulCfg, step, stepAux]

@[simp] theorem multiplication_step_finish_add (v : AddState) (ms as bs : List Bool) :
    multiplicationMachine.step (mulCfg (some .add) v ms [] [] as bs) =
      some (mulCfg (some .restoreX) (v.1, none, none) ms [] [] as
        (if v.1 then true :: bs else bs)) := by
  rcases v with ⟨c, a, b⟩
  cases c <;> simp [multiplicationMachine, mulCfg, step, stepAux]
  all_goals funext k; cases k <;> simp

/-- The adder saves each multiplicand bit while consuming its two input words. -/
theorem multiplication_step_add (v : AddState) (ms xs zs as bs : List Bool)
    (h : xs ≠ [] ∨ zs ≠ []) :
    multiplicationMachine.step (mulCfg (some .add) v ms xs zs as bs) =
      some (mulCfg (some .add)
        (fullAdderCarry (xs.head?.getD false) (zs.head?.getD false) v.1, none, none)
        ms xs.tail zs.tail (if xs = [] then as else xs.head?.getD false :: as)
        (fullAdderBit (xs.head?.getD false) (zs.head?.getD false) v.1 :: bs)) := by
  cases xs with
  | nil =>
    cases zs with
    | nil => simp at h
    | cons z zs =>
      simp [multiplicationMachine, mulCfg, step, stepAux]
      funext k; cases k <;> simp
  | cons x xs =>
    cases zs with
    | nil =>
      simp [multiplicationMachine, mulCfg, step, stepAux]
      funext k; cases k <;> simp
    | cons z zs =>
      simp [multiplicationMachine, mulCfg, step, stepAux]
      funext k; cases k <;> simp


/-- Parsing consumes one transition per bit and one for its delimiter. -/
def multiplication_parse (v : AddState) (ns ms xs zs as bs : List Bool) :
    EvalsToInTime multiplicationMachine.step
      (mulCfg (some .parse) v (Complexity.BitEncoding.frame ns ++ ms) xs zs as bs)
      (some (mulCfg (some .reverseInput) (v.1, some false, v.2.2)
        ms xs zs (ns.reverse ++ as) bs)) (ns.length + 1) := by
  induction ns generalizing v as with
  | nil => simpa [Complexity.BitEncoding.frame] using
      oneStep multiplicationMachine.step (multiplication_step_parse_end v ms xs zs as bs)
  | cons b ns ih =>
      have h := EvalsToInTime.trans multiplicationMachine.step 1 (ns.length + 1) _ _ _
        (oneStep multiplicationMachine.step
          (multiplication_step_parse_bit v b (Complexity.BitEncoding.frame ns ++ ms) xs zs as bs))
        (ih (v.1, some b, v.2.2) (b :: as))
      simpa [Complexity.BitEncoding.frame, List.reverse_cons, List.append_assoc] using h

def multiplication_reverse (v : AddState) (ms xs zs as bs : List Bool) :
    EvalsToInTime multiplicationMachine.step (mulCfg (some .reverseInput) v ms xs zs as bs)
      (some (mulCfg (some .loop) (false, none, none) ms (as.reverse ++ xs) zs [] bs))
      (as.length + 1) := by
  induction as generalizing xs v with
  | nil =>
      simpa using oneStep multiplicationMachine.step (multiplication_step_reverse_nil v ms xs zs bs)
  | cons b as ih =>
      have h := EvalsToInTime.trans multiplicationMachine.step 1 (as.length + 1) _ _ _
        (oneStep multiplicationMachine.step (multiplication_step_reverse_cons v b ms xs zs as bs))
        (ih (v.1, some b, v.2.2) (b :: xs))
      simpa [List.reverse_cons, List.append_assoc] using h

def multiplication_clear (v : AddState) (xs zs : List Bool) :
    EvalsToInTime multiplicationMachine.step (mulCfg (some .clear) v [] xs zs [] [])
      (some (mulCfg none (false, none, none) [] [] zs [] [])) (xs.length + 1) := by
  induction xs generalizing v with
  | nil => simpa using oneStep multiplicationMachine.step (multiplication_step_clear_nil v zs)
  | cons b xs ih =>
      have h := EvalsToInTime.trans multiplicationMachine.step 1 (xs.length + 1) _ _ _
        (oneStep multiplicationMachine.step (multiplication_step_clear_cons v b xs zs))
        (ih (v.1, some b, v.2.2))
      simpa using h

def multiplication_restoreZ (v : AddState) (ms xs zs bs : List Bool) :
    EvalsToInTime multiplicationMachine.step (mulCfg (some .restoreZ) v ms xs zs [] bs)
      (some (mulCfg (some .shift) (false, none, none) ms xs (bs.reverse ++ zs) [] []))
      (bs.length + 1) := by
  induction bs generalizing zs v with
  | nil =>
      simpa using oneStep multiplicationMachine.step (multiplication_step_restoreZ_nil v ms xs zs)
  | cons b bs ih =>
      have h := EvalsToInTime.trans multiplicationMachine.step 1 (bs.length + 1) _ _ _
        (oneStep multiplicationMachine.step (multiplication_step_restoreZ_cons v b ms xs zs bs))
        (ih (v.1, some b, v.2.2) (b :: zs))
      simpa [List.reverse_cons, List.append_assoc] using h

/-- Both temporary reversed words are restored one bit at a time. -/
def multiplication_restore (v : AddState) (ms xs zs as bs : List Bool) :
    EvalsToInTime multiplicationMachine.step (mulCfg (some .restoreX) v ms xs zs as bs)
      (some (mulCfg (some .shift) (false, none, none)
        ms (as.reverse ++ xs) (bs.reverse ++ zs) [] [])) (as.length + bs.length + 2) := by
  induction as generalizing xs v with
  | nil =>
      have h := EvalsToInTime.trans multiplicationMachine.step 1 (bs.length + 1) _ _ _
        (oneStep multiplicationMachine.step (multiplication_step_restoreX_nil v ms xs zs bs))
        (multiplication_restoreZ (v.1, none, v.2.2) ms xs zs bs)
      simpa using h
  | cons b as ih =>
      have h := EvalsToInTime.trans multiplicationMachine.step 1 (as.length + bs.length + 2) _ _ _
        (oneStep multiplicationMachine.step (multiplication_step_restoreX_cons v b ms xs zs as bs))
        (ih (v.1, some b, v.2.2) (b :: xs))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

private theorem mul_addBits_step (c : Bool) (xs zs : List Bool) (h : xs ≠ [] ∨ zs ≠ []) :
    addBits c xs zs =
      fullAdderBit (xs.head?.getD false) (zs.head?.getD false) c ::
        addBits (fullAdderCarry (xs.head?.getD false) (zs.head?.getD false) c)
          xs.tail zs.tail := by
  cases xs <;> cases zs <;> simp_all only [addBits, List.head?_nil, List.head?_cons,
    Option.getD_none, Option.getD_some, List.tail_nil, List.tail_cons, ne_eq, not_true_eq_false,
    or_self]

/-- The embedded adder preserves the multiplicand exactly, while its accumulator
becomes the sum. Both scratch stacks are emptied. -/
def multiplication_add (v : AddState) (ms xs zs as bs : List Bool) :
    EvalsToInTime multiplicationMachine.step (mulCfg (some .add) v ms xs zs as bs)
      (some (mulCfg (some .shift) (false, none, none) ms
        (as.reverse ++ xs) (bs.reverse ++ addBits v.1 xs zs) [] []))
      (3 * (xs.length + zs.length) + as.length + bs.length + 4) := by
  by_cases h : xs = [] ∧ zs = []
  · rcases h with ⟨rfl, rfl⟩
    rcases v with ⟨c, a, b⟩
    cases c with
    | false =>
      have he := EvalsToInTime.trans multiplicationMachine.step 1 (as.length + bs.length + 2)
        _ _ _ (oneStep multiplicationMachine.step
          (multiplication_step_finish_add (false, a, b) ms as bs))
        (multiplication_restore (false, none, none) ms [] [] as bs)
      apply weakenTime (by simpa [addBits] using he)
      simp
    | true =>
      have he := EvalsToInTime.trans multiplicationMachine.step 1
        (as.length + (true :: bs).length + 2) _ _ _
        (oneStep multiplicationMachine.step (multiplication_step_finish_add (true, a, b) ms as bs))
        (multiplication_restore (true, none, none) ms [] [] as (true :: bs))
      simpa [addBits, List.reverse_cons, Nat.add_assoc] using he
  · have hn : xs ≠ [] ∨ zs ≠ [] := by tauto
    let bit := fullAdderBit (xs.head?.getD false) (zs.head?.getD false) v.1
    let carry := fullAdderCarry (xs.head?.getD false) (zs.head?.getD false) v.1
    let as' := if xs = [] then as else xs.head?.getD false :: as
    have hs : multiplicationMachine.step (mulCfg (some .add) v ms xs zs as bs) =
        some (mulCfg (some .add) (carry, none, none) ms xs.tail zs.tail as' (bit :: bs)) :=
      multiplication_step_add v ms xs zs as bs hn
    have he := EvalsToInTime.trans multiplicationMachine.step 1
      (3 * (xs.tail.length + zs.tail.length) + as'.length + (bit :: bs).length + 4) _ _ _
      (oneStep multiplicationMachine.step hs)
      (multiplication_add (carry, none, none) ms xs.tail zs.tail as' (bit :: bs))
    have hx : as'.reverse ++ xs.tail = as.reverse ++ xs := by
      cases xs <;> simp [as', List.reverse_cons, List.append_assoc]
    have hz : (bit :: bs).reverse ++ addBits carry xs.tail zs.tail =
        bs.reverse ++ addBits v.1 xs zs := by
      rw [mul_addBits_step v.1 xs zs hn]
      simp [bit, carry, List.reverse_cons, List.append_assoc]
    rw [hx, hz] at he
    apply weakenTime he
    have hl : xs.tail.length + zs.tail.length + 1 ≤ xs.length + zs.length := by
      cases xs <;> cases zs <;> simp_all
      omega
    have hal : as'.length ≤ as.length + 1 := by
      dsimp [as']; split <;> simp
    simp only [List.length_cons]
    omega
termination_by xs.length + zs.length
decreasing_by
  have hn : xs ≠ [] ∨ zs ≠ [] := by tauto
  cases xs <;> cases zs <;> simp_all
  omega


/-- A uniform bound on all intermediate word lengths makes the loop cost
quadratic in the original binary input lengths. -/
def multiplication_loop (v : AddState) (ms xs zs : List Bool) (B : ℕ)
    (hB : max xs.length zs.length + ms.length ≤ B) :
    EvalsToInTime multiplicationMachine.step (mulCfg (some .loop) v ms xs zs [] [])
      (some (mulCfg none (false, none, none) [] [] (mulLoop xs ms zs) [] []))
      ((6 * B + 6) * ms.length + B + 2) := by
  induction ms generalizing v xs zs with
  | nil =>
      have h := EvalsToInTime.trans multiplicationMachine.step 1 (xs.length + 1) _ _ _
        (oneStep multiplicationMachine.step (multiplication_step_loop_nil v xs zs))
        (multiplication_clear (v.1, none, v.2.2) xs zs)
      apply weakenTime (by simpa [mulLoop] using h)
      simp at hB ⊢
      omega
  | cons b ms ih =>
      have hxl := shiftBits_length_le xs
      cases b with
      | false =>
        have hB' : max (shiftBits xs).length zs.length + ms.length ≤ B := by
          simp only [List.length_cons] at hB
          omega
        have hs := oneStep multiplicationMachine.step
          (multiplication_step_shift (v.1, some false, v.2.2) ms xs zs)
        have hi := ih (false, none, none) (shiftBits xs) zs hB'
        have hsi := EvalsToInTime.trans multiplicationMachine.step 1
          ((6 * B + 6) * ms.length + B + 2) _ _ _ hs hi
        have h := EvalsToInTime.trans multiplicationMachine.step 1
          (((6 * B + 6) * ms.length + B + 2) + 1) _ _ _
          (oneStep multiplicationMachine.step (multiplication_step_loop_false v ms xs zs)) hsi
        apply weakenTime (by simpa [mulLoop] using h)
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      | true =>
        have hzl := addBits_length_le_max false xs zs
        have hB' : max (shiftBits xs).length (addBits false xs zs).length + ms.length ≤ B := by
          simp only [List.length_cons] at hB
          omega
        have ha := multiplication_add (false, none, none) ms xs zs [] []
        simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.add_zero] at ha
        have hs := oneStep multiplicationMachine.step
          (multiplication_step_shift (false, none, none) ms xs (addBits false xs zs))
        have hi := ih (false, none, none) (shiftBits xs) (addBits false xs zs) hB'
        have hsi := EvalsToInTime.trans multiplicationMachine.step 1
          ((6 * B + 6) * ms.length + B + 2) _ _ _ hs hi
        have hasi := EvalsToInTime.trans multiplicationMachine.step
          (3 * (xs.length + zs.length) + 4)
          (((6 * B + 6) * ms.length + B + 2) + 1) _ _ _ ha hsi
        have h := EvalsToInTime.trans multiplicationMachine.step 1
          ((((6 * B + 6) * ms.length + B + 2) + 1) +
            (3 * (xs.length + zs.length) + 4)) _ _ _
          (oneStep multiplicationMachine.step (multiplication_step_loop_true v ms xs zs)) hasi
        apply weakenTime (by simpa [mulLoop] using h)
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hB ⊢
        omega

/-- An explicit quadratic bound before conversion to encoded-input length. -/
def multiplication_outputs (xs ys : List Bool) :
    TM2OutputsInTime multiplicationMachine (Complexity.BitEncoding.frame xs ++ ys)
      (some (mulBits xs ys))
      ((6 * (xs.length + ys.length) + 6) * ys.length +
        (xs.length + ys.length) + 2 + (2 * xs.length + 2)) := by
  have hp := multiplication_parse (false, none, none) xs ys [] [] [] []
  have hr := multiplication_reverse (false, some false, none) ys [] [] xs.reverse []
  have hl := multiplication_loop (false, none, none) ys xs [] (xs.length + ys.length) (by simp)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hp hr hl
  have hpr := EvalsToInTime.trans multiplicationMachine.step (xs.length + 1) (xs.length + 1)
    _ _ _ hp hr
  have h := EvalsToInTime.trans multiplicationMachine.step
    ((xs.length + 1) + (xs.length + 1))
    ((6 * (xs.length + ys.length) + 6) * ys.length + (xs.length + ys.length) + 2)
    _ _ _ hpr hl
  have hi : initList multiplicationMachine (Complexity.BitEncoding.frame xs ++ ys) =
      mulCfg (some .parse) (false, none, none) (Complexity.BitEncoding.frame xs ++ ys) [] [] [] [] := by
    unfold initList mulCfg
    congr 1
    funext k; cases k <;> rfl
  have ho : haltList multiplicationMachine (mulBits xs ys) =
      mulCfg none (false, none, none) [] [] (mulBits xs ys) [] [] := by
    unfold haltList mulCfg
    congr 1
    funext k; cases k <;> rfl
  have ht : (xs.length + 1) + (xs.length + 1) = 2 * xs.length + 2 := by omega
  rw [ht] at h
  unfold TM2OutputsInTime
  simp only [Option.map_some, hi, ho]
  exact h


/-- The complete machine is quadratic in the actual serialized input length. -/
def multiplication_outputs_polynomial (xs ys : List Bool) :
    TM2OutputsInTime multiplicationMachine (Complexity.BitEncoding.frame xs ++ ys)
      (some (mulBits xs ys))
      ((6 * (Complexity.BitEncoding.frame xs ++ ys).length + 6) *
        (Complexity.BitEncoding.frame xs ++ ys).length +
        3 * (Complexity.BitEncoding.frame xs ++ ys).length + 4) := by
  apply weakenTime (multiplication_outputs xs ys)
  simp only [List.length_append, Complexity.BitEncoding.frame_length]
  have hm : (6 * (xs.length + ys.length) + 6) * ys.length ≤
      (6 * (2 * xs.length + 1 + ys.length) + 6) * (2 * xs.length + 1 + ys.length) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Genuine polynomial-time multiplication on the exact framed binary encoding. -/
noncomputable def multiplicationComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat).toFinEncoding
      Complexity.BitEncoding.nat.toFinEncoding (fun n : ℕ × ℕ => n.1 * n.2) where
  tm := multiplicationMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := (Polynomial.C 6 * Polynomial.X + Polynomial.C 6) * Polynomial.X +
    Polynomial.C 3 * Polynomial.X + Polynomial.C 4
  outputsFun n := by
    have h := multiplication_outputs_polynomial
      (Computability.encodeNat n.1) (Computability.encodeNat n.2)
    rw [mulBits_encodeNat] at h
    simpa [Complexity.BitEncoding.nat, Complexity.BitEncoding.prod,
      Complexity.BitEncoding.toFinEncoding, Polynomial.eval_add, Polynomial.eval_mul,
      Equiv.refl, Equiv.symm] using h

theorem fp_multiplication :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat)
      Complexity.BitEncoding.nat (fun n : ℕ × ℕ => n.1 * n.2) :=
  ⟨multiplicationComputable⟩

end PlanarHom.BinaryArithmetic
