import PlanarHom.BinarySubtractionBits
import PlanarHom.BinaryAdditionMachine

/-! # Actual linear-time binary comparison and truncated subtraction TM2 programs -/
namespace PlanarHom.BinaryArithmetic

open Turing Turing.TM2

inductive SubLabel | parse | reverseInput | subtract | clear | trim | restore
  deriving DecidableEq, Fintype

/-- A compile-time Boolean selects comparison or canonical truncated subtraction.
Both programs use only Boolean gates and individual bit-stack operations. -/
def subtractionMachine (compare : Bool) : FinTM2 where
  K := Option Bool
  k₀ := none
  k₁ := none
  Γ _ := Bool
  Λ := SubLabel
  main := .parse
  σ := AddState
  initialState := (false, none, none)
  m
    | .parse => .pop none (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.getD false)
          (.pop none (fun v b => (v.1, b, v.2.2)) <|
            .push (some false) (fun v => v.2.1.getD false) (.goto (fun _ => .parse)))
          (.goto (fun _ => .reverseInput))
    | .reverseInput => .pop (some false) (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push (some true) (fun v => v.2.1.getD false) (.goto (fun _ => .reverseInput)))
          (.load (fun _ => (false, none, none)) (.goto (fun _ => .subtract)))
    | .subtract => .pop (some true) (fun v b => (v.1, b, v.2.2)) <|
        .pop none (fun v b => (v.1, v.2.1, b)) <|
          .branch (fun v => v.2.1.isSome || v.2.2.isSome)
            (.push (some false)
              (fun v => fullSubtractBit (v.2.1.getD false) (v.2.2.getD false) v.1) <|
              .load (fun v => (fullSubtractBorrow (v.2.1.getD false) (v.2.2.getD false) v.1,
                none, none)) (.goto (fun _ => .subtract)))
            (.branch (fun v => compare || v.1)
              (.goto (fun _ => .clear)) (.goto (fun _ => .trim)))
    | .clear => .pop (some false) (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.goto (fun _ => .clear))
          (if compare then .push none (fun v => v.1) (.load (fun _ => (false, none, none)) .halt)
            else .load (fun _ => (false, none, none)) .halt)
    | .trim => .pop (some false) (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.branch (fun v => v.2.1.getD false)
            (.push none (fun _ => true) (.goto (fun _ => .restore)))
            (.goto (fun _ => .trim)))
          (.load (fun _ => (false, none, none)) .halt)
    | .restore => .pop (some false) (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push none (fun v => v.2.1.getD false) (.goto (fun _ => .restore)))
          (.load (fun _ => (false, none, none)) .halt)

def subCfg (compare : Bool) (label : Option SubLabel) (v : AddState)
    (ys bs xs : List Bool) : (subtractionMachine compare).Cfg :=
  ⟨label, v, fun k : Option Bool => match k with
    | none => ys | some false => bs | some true => xs⟩

@[simp] theorem subtraction_step_parse_bit (cmp : Bool) (v : AddState) (b : Bool)
    (ys bs xs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .parse) v (true :: b :: ys) bs xs) =
      some (subCfg cmp (some .parse) (v.1, some b, v.2.2) ys (b :: bs) xs) := by
  simp [subtractionMachine, subCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem subtraction_step_parse_end (cmp : Bool) (v : AddState) (ys bs xs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .parse) v (false :: ys) bs xs) =
      some (subCfg cmp (some .reverseInput) (v.1, some false, v.2.2) ys bs xs) := by
  simp [subtractionMachine, subCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem subtraction_step_reverse_cons (cmp : Bool) (v : AddState) (b : Bool)
    (ys bs xs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .reverseInput) v ys (b :: bs) xs) =
      some (subCfg cmp (some .reverseInput) (v.1, some b, v.2.2) ys bs (b :: xs)) := by
  simp [subtractionMachine, subCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem subtraction_step_reverse_nil (cmp : Bool) (v : AddState) (ys xs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .reverseInput) v ys [] xs) =
      some (subCfg cmp (some .subtract) (false, none, none) ys [] xs) := by
  simp [subtractionMachine, subCfg, step, stepAux]

@[simp] theorem subtraction_step_clear_cons (cmp : Bool) (v : AddState) (b : Bool)
    (bs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .clear) v [] (b :: bs) []) =
      some (subCfg cmp (some .clear) (v.1, some b, v.2.2) [] bs []) := by
  simp [subtractionMachine, subCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem subtraction_step_clear_nil (cmp : Bool) (v : AddState) :
    (subtractionMachine cmp).step (subCfg cmp (some .clear) v [] [] []) =
      some (subCfg cmp none (false, none, none) (if cmp then [v.1] else []) [] []) := by
  cases cmp <;> simp [subtractionMachine, subCfg, step, stepAux]
  all_goals funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem subtraction_step_restore_cons (cmp : Bool) (v : AddState) (b : Bool)
    (ys bs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .restore) v ys (b :: bs) []) =
      some (subCfg cmp (some .restore) (v.1, some b, v.2.2) (b :: ys) bs []) := by
  simp [subtractionMachine, subCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem subtraction_step_restore_nil (cmp : Bool) (v : AddState) (ys : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .restore) v ys [] []) =
      some (subCfg cmp none (false, none, none) ys [] []) := by
  simp [subtractionMachine, subCfg, step, stepAux]

@[simp] theorem subtraction_step_trim_false (cmp : Bool) (v : AddState) (bs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .trim) v [] (false :: bs) []) =
      some (subCfg cmp (some .trim) (v.1, some false, v.2.2) [] bs []) := by
  simp [subtractionMachine, subCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem subtraction_step_trim_true (cmp : Bool) (v : AddState) (bs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .trim) v [] (true :: bs) []) =
      some (subCfg cmp (some .restore) (v.1, some true, v.2.2) [true] bs []) := by
  simp [subtractionMachine, subCfg, step, stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem subtraction_step_trim_nil (cmp : Bool) (v : AddState) :
    (subtractionMachine cmp).step (subCfg cmp (some .trim) v [] [] []) =
      some (subCfg cmp none (false, none, none) [] [] []) := by
  simp [subtractionMachine, subCfg, step, stepAux]

@[simp] theorem subtraction_step_finish (cmp : Bool) (v : AddState) (bs : List Bool) :
    (subtractionMachine cmp).step (subCfg cmp (some .subtract) v [] bs []) =
      some (subCfg cmp (some (if cmp || v.1 then .clear else .trim))
        (v.1, none, none) [] bs []) := by
  cases cmp <;> cases hc : v.1 <;> simp [subtractionMachine, subCfg, step, stepAux, hc]

/-- One transition performs a full subtractor and consumes a bit from each input. -/
theorem subtraction_step_subtract (cmp : Bool) (v : AddState) (xs ys bs : List Bool)
    (h : xs ≠ [] ∨ ys ≠ []) :
    (subtractionMachine cmp).step (subCfg cmp (some .subtract) v ys bs xs) =
      some (subCfg cmp (some .subtract)
        (fullSubtractBorrow (xs.head?.getD false) (ys.head?.getD false) v.1, none, none)
        ys.tail (fullSubtractBit (xs.head?.getD false) (ys.head?.getD false) v.1 :: bs)
        xs.tail) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp [subtractionMachine, subCfg, step, stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp
  | cons x xs =>
    cases ys with
    | nil =>
      simp [subtractionMachine, subCfg, step, stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp
    | cons y ys =>
      simp [subtractionMachine, subCfg, step, stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp

/-- Parsing is charged bit by bit, including the delimiter. -/
def subtraction_parse (cmp : Bool) (v : AddState) (ns ys bs xs : List Bool) :
    EvalsToInTime (subtractionMachine cmp).step
      (subCfg cmp (some .parse) v (Complexity.BitEncoding.frame ns ++ ys) bs xs)
      (some (subCfg cmp (some .reverseInput) (v.1, some false, v.2.2)
        ys (ns.reverse ++ bs) xs)) (ns.length + 1) := by
  induction ns generalizing v bs with
  | nil => simpa [Complexity.BitEncoding.frame] using
      oneStep (subtractionMachine cmp).step (subtraction_step_parse_end cmp v ys bs xs)
  | cons b ns ih =>
      have h := EvalsToInTime.trans (subtractionMachine cmp).step 1 (ns.length + 1) _ _ _
        (oneStep (subtractionMachine cmp).step
          (subtraction_step_parse_bit cmp v b (Complexity.BitEncoding.frame ns ++ ys) bs xs))
        (ih (v.1, some b, v.2.2) (b :: bs))
      simpa [Complexity.BitEncoding.frame, List.reverse_cons, List.append_assoc] using h

def subtraction_reverse (cmp : Bool) (v : AddState) (ys bs xs : List Bool) :
    EvalsToInTime (subtractionMachine cmp).step (subCfg cmp (some .reverseInput) v ys bs xs)
      (some (subCfg cmp (some .subtract) (false, none, none) ys [] (bs.reverse ++ xs)))
      (bs.length + 1) := by
  induction bs generalizing xs v with
  | nil =>
    simpa using oneStep (subtractionMachine cmp).step (subtraction_step_reverse_nil cmp v ys xs)
  | cons b bs ih =>
    have h := EvalsToInTime.trans (subtractionMachine cmp).step 1 (bs.length + 1) _ _ _
      (oneStep (subtractionMachine cmp).step (subtraction_step_reverse_cons cmp v b ys bs xs))
      (ih (v.1, some b, v.2.2) (b :: xs))
    simpa [List.reverse_cons, List.append_assoc] using h

def subtraction_clear (cmp : Bool) (v : AddState) (bs : List Bool) :
    EvalsToInTime (subtractionMachine cmp).step (subCfg cmp (some .clear) v [] bs [])
      (some (subCfg cmp none (false, none, none) (if cmp then [v.1] else []) [] []))
      (bs.length + 1) := by
  induction bs generalizing v with
  | nil => simpa using oneStep (subtractionMachine cmp).step (subtraction_step_clear_nil cmp v)
  | cons b bs ih =>
    have h := EvalsToInTime.trans (subtractionMachine cmp).step 1 (bs.length + 1) _ _ _
      (oneStep (subtractionMachine cmp).step (subtraction_step_clear_cons cmp v b bs))
      (ih (v.1, some b, v.2.2))
    simpa using h

def subtraction_restore (cmp : Bool) (v : AddState) (ys bs : List Bool) :
    EvalsToInTime (subtractionMachine cmp).step (subCfg cmp (some .restore) v ys bs [])
      (some (subCfg cmp none (false, none, none) (bs.reverse ++ ys) [] [])) (bs.length + 1) := by
  induction bs generalizing ys v with
  | nil => simpa using oneStep (subtractionMachine cmp).step (subtraction_step_restore_nil cmp v ys)
  | cons b bs ih =>
    have h := EvalsToInTime.trans (subtractionMachine cmp).step 1 (bs.length + 1) _ _ _
      (oneStep (subtractionMachine cmp).step (subtraction_step_restore_cons cmp v b ys bs))
      (ih (v.1, some b, v.2.2) (b :: ys))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Remove high zeroes and reverse the significant output into canonical order. -/
def subtraction_trim (cmp : Bool) (v : AddState) (bs : List Bool) :
    EvalsToInTime (subtractionMachine cmp).step (subCfg cmp (some .trim) v [] bs [])
      (some (subCfg cmp none (false, none, none) (normalizeBits bs.reverse) [] []))
      (bs.length + 1) := by
  induction bs generalizing v with
  | nil => simpa [normalizeBits] using
      oneStep (subtractionMachine cmp).step (subtraction_step_trim_nil cmp v)
  | cons b bs ih =>
    cases b with
    | false =>
      have h := EvalsToInTime.trans (subtractionMachine cmp).step 1 (bs.length + 1) _ _ _
        (oneStep (subtractionMachine cmp).step (subtraction_step_trim_false cmp v bs))
        (ih (v.1, some false, v.2.2))
      simpa [List.reverse_cons] using h
    | true =>
      have h := EvalsToInTime.trans (subtractionMachine cmp).step 1 (bs.length + 1) _ _ _
        (oneStep (subtractionMachine cmp).step (subtraction_step_trim_true cmp v bs))
        (subtraction_restore cmp (v.1, some true, v.2.2) [true] bs)
      simpa [List.reverse_cons] using h

/-- The compile-time mode decides whether to expose the final comparison bit or
the normalized, zero-truncated difference. -/
def subtractionResult (cmp borrow : Bool) (xs : List Bool) : List Bool :=
  if cmp then [borrow] else if borrow then [] else normalizeBits xs

def subtraction_finish (cmp : Bool) (v : AddState) (bs : List Bool) :
    EvalsToInTime (subtractionMachine cmp).step (subCfg cmp (some .subtract) v [] bs [])
      (some (subCfg cmp none (false, none, none) (subtractionResult cmp v.1 bs.reverse) [] []))
      (bs.length + 2) := by
  rcases v with ⟨c, a, b⟩
  cases cmp <;> cases c
  · have h := EvalsToInTime.trans (subtractionMachine false).step 1 (bs.length + 1) _ _ _
      (oneStep (subtractionMachine false).step (subtraction_step_finish false (false, a, b) bs))
      (subtraction_trim false (false, none, none) bs)
    simpa [subtractionResult] using h
  · have h := EvalsToInTime.trans (subtractionMachine false).step 1 (bs.length + 1) _ _ _
      (oneStep (subtractionMachine false).step (subtraction_step_finish false (true, a, b) bs))
      (subtraction_clear false (true, none, none) bs)
    simpa [subtractionResult] using h
  · have h := EvalsToInTime.trans (subtractionMachine true).step 1 (bs.length + 1) _ _ _
      (oneStep (subtractionMachine true).step (subtraction_step_finish true (false, a, b) bs))
      (subtraction_clear true (false, none, none) bs)
    simpa [subtractionResult] using h
  · have h := EvalsToInTime.trans (subtractionMachine true).step 1 (bs.length + 1) _ _ _
      (oneStep (subtractionMachine true).step (subtraction_step_finish true (true, a, b) bs))
      (subtraction_clear true (true, none, none) bs)
    simpa [subtractionResult] using h

private theorem subtractWithBorrow_step (c : Bool) (xs ys : List Bool) (h : xs ≠ [] ∨ ys ≠ []) :
    subtractWithBorrow c xs ys =
      let r := subtractWithBorrow
        (fullSubtractBorrow (xs.head?.getD false) (ys.head?.getD false) c) xs.tail ys.tail
      (r.1, fullSubtractBit (xs.head?.getD false) (ys.head?.getD false) c :: r.2) := by
  cases xs <;> cases ys <;> simp_all only [subtractWithBorrow, List.head?_nil, List.head?_cons,
    Option.getD_none, Option.getD_some, List.tail_nil, List.tail_cons, ne_eq, not_true_eq_false,
    or_self]

/-- Linear-time bit subtraction, including comparison/output normalization. -/
def subtraction_run (cmp : Bool) (v : AddState) (xs ys bs : List Bool) :
    EvalsToInTime (subtractionMachine cmp).step (subCfg cmp (some .subtract) v ys bs xs)
      (some (subCfg cmp none (false, none, none)
        (subtractionResult cmp (subtractWithBorrow v.1 xs ys).1
          (bs.reverse ++ (subtractWithBorrow v.1 xs ys).2)) [] []))
      (2 * (xs.length + ys.length) + bs.length + 2) := by
  by_cases h : xs = [] ∧ ys = []
  · rcases h with ⟨rfl, rfl⟩
    simpa [subtractWithBorrow] using subtraction_finish cmp v bs
  · have hn : xs ≠ [] ∨ ys ≠ [] := by tauto
    let bit := fullSubtractBit (xs.head?.getD false) (ys.head?.getD false) v.1
    let borrow := fullSubtractBorrow (xs.head?.getD false) (ys.head?.getD false) v.1
    have hs := subtraction_step_subtract cmp v xs ys bs hn
    have he := EvalsToInTime.trans (subtractionMachine cmp).step 1
      (2 * (xs.tail.length + ys.tail.length) + (bit :: bs).length + 2) _ _ _
      (oneStep (subtractionMachine cmp).step hs)
      (subtraction_run cmp (borrow, none, none) xs.tail ys.tail (bit :: bs))
    have ho : subtractionResult cmp (subtractWithBorrow borrow xs.tail ys.tail).1
        ((bit :: bs).reverse ++ (subtractWithBorrow borrow xs.tail ys.tail).2) =
        subtractionResult cmp (subtractWithBorrow v.1 xs ys).1
          (bs.reverse ++ (subtractWithBorrow v.1 xs ys).2) := by
      rw [subtractWithBorrow_step v.1 xs ys hn]
      simp [bit, borrow, List.reverse_cons, List.append_assoc]
    rw [ho] at he
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


/-- Complete framed-input execution of the comparison/subtraction program. -/
def subtraction_outputs (cmp : Bool) (xs ys : List Bool) :
    TM2OutputsInTime (subtractionMachine cmp) (Complexity.BitEncoding.frame xs ++ ys)
      (some (subtractionResult cmp (subtractWithBorrow false xs ys).1
        (subtractWithBorrow false xs ys).2)) (4 * xs.length + 2 * ys.length + 4) := by
  have hp := subtraction_parse cmp (false, none, none) xs ys [] []
  have hr := subtraction_reverse cmp (false, some false, none) ys xs.reverse []
  have hs := subtraction_run cmp (false, none, none) xs ys []
  simp only [List.append_nil, List.reverse_nil, List.nil_append, List.length_nil,
    Nat.add_zero, List.reverse_reverse, List.length_reverse] at hp hr hs
  have hpr := EvalsToInTime.trans (subtractionMachine cmp).step
    (xs.length + 1) (xs.length + 1) _ _ _ hp hr
  have h := EvalsToInTime.trans (subtractionMachine cmp).step
    ((xs.length + 1) + (xs.length + 1)) (2 * (xs.length + ys.length) + 2) _ _ _ hpr hs
  have hi : initList (subtractionMachine cmp) (Complexity.BitEncoding.frame xs ++ ys) =
      subCfg cmp (some .parse) (false, none, none) (Complexity.BitEncoding.frame xs ++ ys) [] [] := by
    unfold initList subCfg
    congr 1
    funext k; rcases k with _ | (_ | _) <;> rfl
  have ho (out : List Bool) : haltList (subtractionMachine cmp) out =
      subCfg cmp none (false, none, none) out [] [] := by
    unfold haltList subCfg
    congr 1
    funext k; rcases k with _ | (_ | _) <;> rfl
  have ht : (2 * (xs.length + ys.length) + 2) + ((xs.length + 1) + (xs.length + 1)) =
      4 * xs.length + 2 * ys.length + 4 := by omega
  rw [ht] at h
  simpa [TM2OutputsInTime, hi, ho] using h

/-- Truncated subtraction of natural numbers in linear binary input time. -/
noncomputable def subtractionComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat).toFinEncoding
      Complexity.BitEncoding.nat.toFinEncoding (fun p : ℕ × ℕ => p.1 - p.2) where
  tm := subtractionMachine false
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun p := by
    have h := subtraction_outputs false (Computability.encodeNat p.1) (Computability.encodeNat p.2)
    have he : subtractionResult false
        (subtractWithBorrow false (Computability.encodeNat p.1) (Computability.encodeNat p.2)).1
        (subtractWithBorrow false (Computability.encodeNat p.1) (Computability.encodeNat p.2)).2 =
        Computability.encodeNat (p.1 - p.2) := subBits_encodeNat p.1 p.2
    rw [he] at h
    have ht : 4 * (Computability.encodeNat p.1).length +
        2 * (Computability.encodeNat p.2).length + 4 =
        2 * (2 * (Computability.encodeNat p.1).length +
          (Computability.encodeNat p.2).length + 1) + 2 := by omega
    rw [ht] at h
    simpa [Complexity.BitEncoding.nat, Complexity.BitEncoding.prod,
      Complexity.BitEncoding.toFinEncoding, Complexity.BitEncoding.frame_length,
      Polynomial.eval_add, Polynomial.eval_mul, Equiv.refl, Equiv.symm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Strict comparison of binary natural numbers in linear input time. -/
noncomputable def comparisonComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat).toFinEncoding
      Complexity.BitEncoding.bool.toFinEncoding (fun p : ℕ × ℕ => decide (p.1 < p.2)) where
  tm := subtractionMachine true
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun p := by
    have h := subtraction_outputs true (Computability.encodeNat p.1) (Computability.encodeNat p.2)
    have he := lessBits_encodeNat p.1 p.2
    simp only [lessBits] at he
    simp only [subtractionResult, ↓reduceIte, he] at h
    have ht : 4 * (Computability.encodeNat p.1).length +
        2 * (Computability.encodeNat p.2).length + 4 =
        2 * (2 * (Computability.encodeNat p.1).length +
          (Computability.encodeNat p.2).length + 1) + 2 := by omega
    rw [ht] at h
    simpa [Complexity.BitEncoding.nat, Complexity.BitEncoding.bool, Complexity.BitEncoding.prod,
      Complexity.BitEncoding.toFinEncoding, Complexity.BitEncoding.frame_length,
      Polynomial.eval_add, Polynomial.eval_mul, Equiv.refl, Equiv.symm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem fp_subtraction :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat)
      Complexity.BitEncoding.nat (fun p : ℕ × ℕ => p.1 - p.2) := ⟨subtractionComputable⟩

theorem fp_comparison :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat)
      Complexity.BitEncoding.bool (fun p : ℕ × ℕ => decide (p.1 < p.2)) := ⟨comparisonComputable⟩

end PlanarHom.BinaryArithmetic
