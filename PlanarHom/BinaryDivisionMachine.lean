import PlanarHom.BinaryDivisionBits
import PlanarHom.BinarySubtractionMachine

/-! # A genuine binary long-division TM2 -/
namespace PlanarHom.BinaryArithmetic
open Turing Turing.TM2

inductive DivStack | ds | ms | qs | rs | sd | sr | diff | out deriving DecidableEq, Fintype
inductive DivLabel
  | parse | check | zeroCopy | zeroFinish | loop | subtract | restoreD | choose
  | clearDiff | restoreOld | clearOld | trim | restoreDiff | pushQ | clearD
  | reverseR | outputR | delimiter | reverseQ | outputQ
  deriving DecidableEq, Fintype

structure DivData where
  ds : List Bool
  ms : List Bool
  qs : List Bool
  rs : List Bool
  sd : List Bool
  sr : List Bool
  diff : List Bool
  out : List Bool

def DivData.stacks (s : DivData) : DivStack → List Bool
  | .ds => s.ds | .ms => s.ms | .qs => s.qs | .rs => s.rs
  | .sd => s.sd | .sr => s.sr | .diff => s.diff | .out => s.out

abbrev DivStmt := Stmt (fun _ : DivStack => Bool) DivLabel AddState

def divMove (src dst : DivStack) (again next : DivLabel) : DivStmt :=
  .pop src (fun v b => (v.1, b, v.2.2)) <|
    .branch (fun v => v.2.1.isSome)
      (.push dst (fun v => v.2.1.getD false) (.goto (fun _ => again)))
      (.goto (fun _ => next))

def divClear (src : DivStack) (again next : DivLabel) : DivStmt :=
  .pop src (fun v b => (v.1, b, v.2.2)) <|
    .branch (fun v => v.2.1.isSome) (.goto (fun _ => again)) (.goto (fun _ => next))

/-- A canonical binary cons requires only peeking at whether the old word is empty. -/
def divCanonicalCons (dst : DivStack) (bit : AddState → Bool) (next : DivStmt) : DivStmt :=
  .peek dst (fun v b => (v.1, v.2.1, b)) <|
    .branch (fun v => bit v || v.2.2.isSome) (.push dst bit next) next

def divisionMachine : FinTM2 where
  K := DivStack
  k₀ := .ds
  k₁ := .out
  Γ _ := Bool
  Λ := DivLabel
  main := .parse
  σ := AddState
  initialState := (false, none, none)
  m
    | .parse => .pop .ds (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.getD false)
          (.pop .ds (fun v b => (v.1, b, v.2.2)) <|
            .push .ms (fun v => v.2.1.getD false) (.goto (fun _ => .parse)))
          (.goto (fun _ => .check))
    | .check => .peek .ds (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.load (fun _ => (false, none, none)) (.goto (fun _ => .loop)))
          (.goto (fun _ => .zeroCopy))
    | .zeroCopy => divMove .ms .out .zeroCopy .zeroFinish
    | .zeroFinish => .push .out (fun _ => false) (.load (fun _ => (false, none, none)) .halt)
    | .loop => .pop .ms (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (divCanonicalCons .rs (fun v => v.2.1.getD false)
            (.load (fun _ => (false, none, none)) (.goto (fun _ => .subtract))))
          (.goto (fun _ => .clearD))
    | .subtract =>
      let next : DivStmt :=
        .branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (.push .diff (fun v => fullSubtractBit (v.2.1.getD false) (v.2.2.getD false) v.1) <|
            .load (fun v => (fullSubtractBorrow (v.2.1.getD false) (v.2.2.getD false) v.1,
              none, none)) (.goto (fun _ => .subtract)))
          (.goto (fun _ => .restoreD))
      let saveD : DivStmt := .branch (fun v => v.2.2.isSome)
        (.push .sd (fun v => v.2.2.getD false) next) next
      .pop .rs (fun v b => (v.1, b, v.2.2)) <|
        .pop .ds (fun v b => (v.1, v.2.1, b)) <|
          .branch (fun v => v.2.1.isSome)
            (.push .sr (fun v => v.2.1.getD false) saveD) saveD
    | .restoreD => divMove .sd .ds .restoreD .choose
    | .choose => .branch (fun v => v.1) (.goto (fun _ => .clearDiff)) (.goto (fun _ => .clearOld))
    | .clearDiff => divClear .diff .clearDiff .restoreOld
    | .restoreOld => divMove .sr .rs .restoreOld .pushQ
    | .clearOld => divClear .sr .clearOld .trim
    | .trim => .pop .diff (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.branch (fun v => v.2.1.getD false)
            (.push .rs (fun _ => true) (.goto (fun _ => .restoreDiff)))
            (.goto (fun _ => .trim)))
          (.goto (fun _ => .pushQ))
    | .restoreDiff => divMove .diff .rs .restoreDiff .pushQ
    | .pushQ => divCanonicalCons .qs (fun v => !v.1)
        (.load (fun _ => (false, none, none)) (.goto (fun _ => .loop)))
    | .clearD => divClear .ds .clearD .reverseR
    | .reverseR => divMove .rs .sr .reverseR .outputR
    | .outputR => divMove .sr .out .outputR .delimiter
    | .delimiter => .push .out (fun _ => false) (.goto (fun _ => .reverseQ))
    | .reverseQ => divMove .qs .sd .reverseQ .outputQ
    | .outputQ => .pop .sd (fun v b => (v.1, b, v.2.2)) <|
        .branch (fun v => v.2.1.isSome)
          (.push .out (fun v => v.2.1.getD false) <|
            .push .out (fun _ => true) (.goto (fun _ => .outputQ)))
          (.load (fun _ => (false, none, none)) .halt)

def divCfg (l : Option DivLabel) (v : AddState) (s : DivData) : divisionMachine.Cfg :=
  ⟨l, v, s.stacks⟩

@[simp] theorem division_step_zeroCopy_cons (v : AddState) (s : DivData) (b : Bool) (as bs : List Bool) :
    divisionMachine.step (divCfg (some .zeroCopy) v {s with ms := b :: as, out := bs}) =
      some (divCfg (some .zeroCopy) (v.1, some b, v.2.2) {s with ms := as, out := b :: bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_zeroCopy_nil (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .zeroCopy) v {s with ms := [], out := bs}) =
      some (divCfg (some .zeroFinish) (v.1, none, v.2.2) {s with ms := [], out := bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]

/-- Exact bit-by-bit stack transfer for this finite program stage. -/
def division_zeroCopy (v : AddState) (s : DivData) (as bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .zeroCopy) v {s with ms := as, out := bs})
      (some (divCfg (some .zeroFinish) (v.1, none, v.2.2)
        {s with ms := [], out := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep divisionMachine.step (division_step_zeroCopy_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_zeroCopy_cons v s b as bs))
      (ih (v.1, some b, v.2.2) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem division_step_restoreD_cons (v : AddState) (s : DivData) (b : Bool) (as bs : List Bool) :
    divisionMachine.step (divCfg (some .restoreD) v {s with sd := b :: as, ds := bs}) =
      some (divCfg (some .restoreD) (v.1, some b, v.2.2) {s with sd := as, ds := b :: bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_restoreD_nil (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .restoreD) v {s with sd := [], ds := bs}) =
      some (divCfg (some .choose) (v.1, none, v.2.2) {s with sd := [], ds := bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]

/-- Exact bit-by-bit stack transfer for this finite program stage. -/
def division_restoreD (v : AddState) (s : DivData) (as bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .restoreD) v {s with sd := as, ds := bs})
      (some (divCfg (some .choose) (v.1, none, v.2.2)
        {s with sd := [], ds := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep divisionMachine.step (division_step_restoreD_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_restoreD_cons v s b as bs))
      (ih (v.1, some b, v.2.2) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem division_step_restoreOld_cons (v : AddState) (s : DivData) (b : Bool) (as bs : List Bool) :
    divisionMachine.step (divCfg (some .restoreOld) v {s with sr := b :: as, rs := bs}) =
      some (divCfg (some .restoreOld) (v.1, some b, v.2.2) {s with sr := as, rs := b :: bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_restoreOld_nil (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .restoreOld) v {s with sr := [], rs := bs}) =
      some (divCfg (some .pushQ) (v.1, none, v.2.2) {s with sr := [], rs := bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]

/-- Exact bit-by-bit stack transfer for this finite program stage. -/
def division_restoreOld (v : AddState) (s : DivData) (as bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .restoreOld) v {s with sr := as, rs := bs})
      (some (divCfg (some .pushQ) (v.1, none, v.2.2)
        {s with sr := [], rs := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep divisionMachine.step (division_step_restoreOld_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_restoreOld_cons v s b as bs))
      (ih (v.1, some b, v.2.2) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem division_step_restoreDiff_cons (v : AddState) (s : DivData) (b : Bool) (as bs : List Bool) :
    divisionMachine.step (divCfg (some .restoreDiff) v {s with diff := b :: as, rs := bs}) =
      some (divCfg (some .restoreDiff) (v.1, some b, v.2.2) {s with diff := as, rs := b :: bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_restoreDiff_nil (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .restoreDiff) v {s with diff := [], rs := bs}) =
      some (divCfg (some .pushQ) (v.1, none, v.2.2) {s with diff := [], rs := bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]

/-- Exact bit-by-bit stack transfer for this finite program stage. -/
def division_restoreDiff (v : AddState) (s : DivData) (as bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .restoreDiff) v {s with diff := as, rs := bs})
      (some (divCfg (some .pushQ) (v.1, none, v.2.2)
        {s with diff := [], rs := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep divisionMachine.step (division_step_restoreDiff_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_restoreDiff_cons v s b as bs))
      (ih (v.1, some b, v.2.2) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem division_step_reverseR_cons (v : AddState) (s : DivData) (b : Bool) (as bs : List Bool) :
    divisionMachine.step (divCfg (some .reverseR) v {s with rs := b :: as, sr := bs}) =
      some (divCfg (some .reverseR) (v.1, some b, v.2.2) {s with rs := as, sr := b :: bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_reverseR_nil (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .reverseR) v {s with rs := [], sr := bs}) =
      some (divCfg (some .outputR) (v.1, none, v.2.2) {s with rs := [], sr := bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]

/-- Exact bit-by-bit stack transfer for this finite program stage. -/
def division_reverseR (v : AddState) (s : DivData) (as bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .reverseR) v {s with rs := as, sr := bs})
      (some (divCfg (some .outputR) (v.1, none, v.2.2)
        {s with rs := [], sr := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep divisionMachine.step (division_step_reverseR_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_reverseR_cons v s b as bs))
      (ih (v.1, some b, v.2.2) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem division_step_outputR_cons (v : AddState) (s : DivData) (b : Bool) (as bs : List Bool) :
    divisionMachine.step (divCfg (some .outputR) v {s with sr := b :: as, out := bs}) =
      some (divCfg (some .outputR) (v.1, some b, v.2.2) {s with sr := as, out := b :: bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_outputR_nil (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .outputR) v {s with sr := [], out := bs}) =
      some (divCfg (some .delimiter) (v.1, none, v.2.2) {s with sr := [], out := bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]

/-- Exact bit-by-bit stack transfer for this finite program stage. -/
def division_outputR (v : AddState) (s : DivData) (as bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .outputR) v {s with sr := as, out := bs})
      (some (divCfg (some .delimiter) (v.1, none, v.2.2)
        {s with sr := [], out := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep divisionMachine.step (division_step_outputR_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_outputR_cons v s b as bs))
      (ih (v.1, some b, v.2.2) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem division_step_reverseQ_cons (v : AddState) (s : DivData) (b : Bool) (as bs : List Bool) :
    divisionMachine.step (divCfg (some .reverseQ) v {s with qs := b :: as, sd := bs}) =
      some (divCfg (some .reverseQ) (v.1, some b, v.2.2) {s with qs := as, sd := b :: bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_reverseQ_nil (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .reverseQ) v {s with qs := [], sd := bs}) =
      some (divCfg (some .outputQ) (v.1, none, v.2.2) {s with qs := [], sd := bs}) := by
  simp [divisionMachine, divMove, divCfg, DivData.stacks, step, stepAux]

/-- Exact bit-by-bit stack transfer for this finite program stage. -/
def division_reverseQ (v : AddState) (s : DivData) (as bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .reverseQ) v {s with qs := as, sd := bs})
      (some (divCfg (some .outputQ) (v.1, none, v.2.2)
        {s with qs := [], sd := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep divisionMachine.step (division_step_reverseQ_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_reverseQ_cons v s b as bs))
      (ih (v.1, some b, v.2.2) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem division_step_clearDiff_cons (v : AddState) (s : DivData) (b : Bool) (as : List Bool) :
    divisionMachine.step (divCfg (some .clearDiff) v {s with diff := b :: as}) =
      some (divCfg (some .clearDiff) (v.1, some b, v.2.2) {s with diff := as}) := by
  simp [divisionMachine, divClear, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_clearDiff_nil (v : AddState) (s : DivData) :
    divisionMachine.step (divCfg (some .clearDiff) v {s with diff := []}) =
      some (divCfg (some .restoreOld) (v.1, none, v.2.2) {s with diff := []}) := by
  simp [divisionMachine, divClear, divCfg, DivData.stacks, step, stepAux]

def division_clearDiff (v : AddState) (s : DivData) (as : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .clearDiff) v {s with diff := as})
      (some (divCfg (some .restoreOld) (v.1, none, v.2.2) {s with diff := []})) (as.length + 1) := by
  induction as generalizing v with
  | nil => simpa using oneStep divisionMachine.step (division_step_clearDiff_nil v s)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_clearDiff_cons v s b as))
      (ih (v.1, some b, v.2.2))
    simpa using h

@[simp] theorem division_step_clearOld_cons (v : AddState) (s : DivData) (b : Bool) (as : List Bool) :
    divisionMachine.step (divCfg (some .clearOld) v {s with sr := b :: as}) =
      some (divCfg (some .clearOld) (v.1, some b, v.2.2) {s with sr := as}) := by
  simp [divisionMachine, divClear, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_clearOld_nil (v : AddState) (s : DivData) :
    divisionMachine.step (divCfg (some .clearOld) v {s with sr := []}) =
      some (divCfg (some .trim) (v.1, none, v.2.2) {s with sr := []}) := by
  simp [divisionMachine, divClear, divCfg, DivData.stacks, step, stepAux]

def division_clearOld (v : AddState) (s : DivData) (as : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .clearOld) v {s with sr := as})
      (some (divCfg (some .trim) (v.1, none, v.2.2) {s with sr := []})) (as.length + 1) := by
  induction as generalizing v with
  | nil => simpa using oneStep divisionMachine.step (division_step_clearOld_nil v s)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_clearOld_cons v s b as))
      (ih (v.1, some b, v.2.2))
    simpa using h

@[simp] theorem division_step_clearD_cons (v : AddState) (s : DivData) (b : Bool) (as : List Bool) :
    divisionMachine.step (divCfg (some .clearD) v {s with ds := b :: as}) =
      some (divCfg (some .clearD) (v.1, some b, v.2.2) {s with ds := as}) := by
  simp [divisionMachine, divClear, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_clearD_nil (v : AddState) (s : DivData) :
    divisionMachine.step (divCfg (some .clearD) v {s with ds := []}) =
      some (divCfg (some .reverseR) (v.1, none, v.2.2) {s with ds := []}) := by
  simp [divisionMachine, divClear, divCfg, DivData.stacks, step, stepAux]

def division_clearD (v : AddState) (s : DivData) (as : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .clearD) v {s with ds := as})
      (some (divCfg (some .reverseR) (v.1, none, v.2.2) {s with ds := []})) (as.length + 1) := by
  induction as generalizing v with
  | nil => simpa using oneStep divisionMachine.step (division_step_clearD_nil v s)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_clearD_cons v s b as))
      (ih (v.1, some b, v.2.2))
    simpa using h


@[simp] theorem division_step_trim_false (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .trim) v {s with rs := [], diff := false :: bs}) =
      some (divCfg (some .trim) (v.1, some false, v.2.2) {s with rs := [], diff := bs}) := by
  simp [divisionMachine, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_trim_true (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .trim) v {s with rs := [], diff := true :: bs}) =
      some (divCfg (some .restoreDiff) (v.1, some true, v.2.2) {s with rs := [true], diff := bs}) := by
  simp [divisionMachine, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_trim_nil (v : AddState) (s : DivData) :
    divisionMachine.step (divCfg (some .trim) v {s with rs := [], diff := []}) =
      some (divCfg (some .pushQ) (v.1, none, v.2.2) {s with rs := [], diff := []}) := by
  simp [divisionMachine, divCfg, DivData.stacks, step, stepAux]

/-- Canonicalize the saved difference, still preserving the borrow register. -/
def division_trim (v : AddState) (s : DivData) (bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .trim) v {s with rs := [], diff := bs})
      (some (divCfg (some .pushQ) (v.1, none, v.2.2)
        {s with rs := normalizeBits bs.reverse, diff := []})) (bs.length + 1) := by
  induction bs generalizing v with
  | nil => simpa [normalizeBits] using oneStep divisionMachine.step (division_step_trim_nil v s)
  | cons b bs ih =>
    cases b with
    | false =>
      have h := EvalsToInTime.trans divisionMachine.step 1 (bs.length + 1) _ _ _
        (oneStep divisionMachine.step (division_step_trim_false v s bs))
        (ih (v.1, some false, v.2.2))
      simpa [List.reverse_cons] using h
    | true =>
      have h := EvalsToInTime.trans divisionMachine.step 1 (bs.length + 1) _ _ _
        (oneStep divisionMachine.step (division_step_trim_true v s bs))
        (division_restoreDiff (v.1, some true, v.2.2) s bs [true])
      simpa [List.reverse_cons] using h

@[simp] theorem division_step_choose (v : AddState) (s : DivData) :
    divisionMachine.step (divCfg (some .choose) v s) =
      some (divCfg (some (if v.1 then .clearDiff else .clearOld)) v s) := by
  cases h : v.1 <;> simp [divisionMachine, divCfg, step, stepAux, h]

/-- The post-subtraction workspace. The numerator stream, quotient, and eventual
output stack are untouched by this subroutine. -/
def divWork (s : DivData) (ds rs sd sr diff : List Bool) : DivData :=
  {s with ds := ds, rs := rs, sd := sd, sr := sr, diff := diff}

/-- Restore the divisor and select either the original remainder on borrow or
the canonical difference without borrow. -/
def division_finish_sub (c : Bool) (s : DivData) (sd sr df : List Bool) :
    EvalsToInTime divisionMachine.step
      (divCfg (some .restoreD) (c, none, none) (divWork s [] [] sd sr df))
      (some (divCfg (some .pushQ) (c, none, none)
        (divWork s sd.reverse (if c then sr.reverse else normalizeBits df.reverse) [] [] [])))
      (sd.length + sr.length + df.length + 4) := by
  have hd := division_restoreD (c, none, none) {s with rs := [], sr := sr, diff := df} sd []
  simp only [List.append_nil] at hd
  have hc := oneStep divisionMachine.step
    (division_step_choose (c, none, none) (divWork s sd.reverse [] [] sr df))
  cases c with
  | false =>
    have ho := division_clearOld (false, none, none)
      (divWork s sd.reverse [] [] sr df) sr
    have ht := division_trim (false, none, none)
      (divWork s sd.reverse [] [] [] df) df
    have hot := EvalsToInTime.trans divisionMachine.step (sr.length + 1) (df.length + 1)
      _ _ _ ho ht
    have hcot := EvalsToInTime.trans divisionMachine.step 1
      ((df.length + 1) + (sr.length + 1)) _ _ _ hc hot
    have hall := EvalsToInTime.trans divisionMachine.step (sd.length + 1)
      (((df.length + 1) + (sr.length + 1)) + 1) _ _ _ hd hcot
    simpa [divWork, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  | true =>
    have hf := division_clearDiff (true, none, none)
      (divWork s sd.reverse [] [] sr df) df
    have hr := division_restoreOld (true, none, none)
      (divWork s sd.reverse [] [] sr []) sr []
    have hfr := EvalsToInTime.trans divisionMachine.step (df.length + 1) (sr.length + 1)
      _ _ _ hf hr
    have hcfr := EvalsToInTime.trans divisionMachine.step 1
      ((sr.length + 1) + (df.length + 1)) _ _ _ hc hfr
    have hall := EvalsToInTime.trans divisionMachine.step (sd.length + 1)
      (((sr.length + 1) + (df.length + 1)) + 1) _ _ _ hd hcfr
    simpa [divWork, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

@[simp] theorem division_step_subtract_nil (v : AddState) (s : DivData) (sd sr df : List Bool) :
    divisionMachine.step (divCfg (some .subtract) v (divWork s [] [] sd sr df)) =
      some (divCfg (some .restoreD) (v.1, none, none) (divWork s [] [] sd sr df)) := by
  simp [divisionMachine, divWork, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

/-- A full-subtractor transition additionally preserves both original operands. -/
theorem division_step_subtract (v : AddState) (s : DivData) (xs ys sd sr df : List Bool)
    (h : xs ≠ [] ∨ ys ≠ []) :
    divisionMachine.step (divCfg (some .subtract) v (divWork s ys xs sd sr df)) =
      some (divCfg (some .subtract)
        (fullSubtractBorrow (xs.head?.getD false) (ys.head?.getD false) v.1, none, none)
        (divWork s ys.tail xs.tail
          (if ys = [] then sd else ys.head?.getD false :: sd)
          (if xs = [] then sr else xs.head?.getD false :: sr)
          (fullSubtractBit (xs.head?.getD false) (ys.head?.getD false) v.1 :: df))) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp [divisionMachine, divWork, divCfg, DivData.stacks, step, stepAux]
      funext k; cases k <;> simp [DivData.stacks]
  | cons x xs =>
    cases ys with
    | nil =>
      simp [divisionMachine, divWork, divCfg, DivData.stacks, step, stepAux]
      funext k; cases k <;> simp [DivData.stacks]
    | cons y ys =>
      simp [divisionMachine, divWork, divCfg, DivData.stacks, step, stepAux]
      funext k; cases k <;> simp [DivData.stacks]

private theorem div_subtractWithBorrow_step (c : Bool) (xs ys : List Bool) (h : xs ≠ [] ∨ ys ≠ []) :
    subtractWithBorrow c xs ys =
      let r := subtractWithBorrow
        (fullSubtractBorrow (xs.head?.getD false) (ys.head?.getD false) c) xs.tail ys.tail
      (r.1, fullSubtractBit (xs.head?.getD false) (ys.head?.getD false) c :: r.2) := by
  cases xs <;> cases ys <;> simp_all only [subtractWithBorrow, List.head?_nil, List.head?_cons,
    Option.getD_none, Option.getD_some, List.tail_nil, List.tail_cons, ne_eq, not_true_eq_false,
    or_self]

/-- One linear-time trial subtraction restores the original remainder on borrow;
otherwise it keeps the normalized difference. The divisor is always restored. -/
def division_subtract (v : AddState) (s : DivData) (xs ys sd sr df : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .subtract) v (divWork s ys xs sd sr df))
      (some (divCfg (some .pushQ) ((subtractWithBorrow v.1 xs ys).1, none, none)
        (divWork s (sd.reverse ++ ys)
          (if (subtractWithBorrow v.1 xs ys).1 then sr.reverse ++ xs
            else normalizeBits (df.reverse ++ (subtractWithBorrow v.1 xs ys).2)) [] [] [])))
      (4 * (xs.length + ys.length) + sd.length + sr.length + df.length + 5) := by
  by_cases h : xs = [] ∧ ys = []
  · rcases h with ⟨rfl, rfl⟩
    have he := EvalsToInTime.trans divisionMachine.step 1
      (sd.length + sr.length + df.length + 4) _ _ _
      (oneStep divisionMachine.step (division_step_subtract_nil v s sd sr df))
      (division_finish_sub v.1 s sd sr df)
    simpa [subtractWithBorrow, Nat.add_assoc] using he
  · have hn : xs ≠ [] ∨ ys ≠ [] := by tauto
    let bit := fullSubtractBit (xs.head?.getD false) (ys.head?.getD false) v.1
    let borrow := fullSubtractBorrow (xs.head?.getD false) (ys.head?.getD false) v.1
    let sd' := if ys = [] then sd else ys.head?.getD false :: sd
    let sr' := if xs = [] then sr else xs.head?.getD false :: sr
    have hs := division_step_subtract v s xs ys sd sr df hn
    have he := EvalsToInTime.trans divisionMachine.step 1
      (4 * (xs.tail.length + ys.tail.length) + sd'.length + sr'.length + (bit :: df).length + 5)
      _ _ _ (oneStep divisionMachine.step hs)
      (division_subtract (borrow, none, none) s xs.tail ys.tail sd' sr' (bit :: df))
    have hd : sd'.reverse ++ ys.tail = sd.reverse ++ ys := by
      cases ys <;> simp [sd', List.reverse_cons, List.append_assoc]
    have hr : sr'.reverse ++ xs.tail = sr.reverse ++ xs := by
      cases xs <;> simp [sr', List.reverse_cons, List.append_assoc]
    rw [hd, hr] at he
    have hout : divCfg (some .pushQ) ((subtractWithBorrow borrow xs.tail ys.tail).1, none, none)
        (divWork s (sd.reverse ++ ys)
          (if (subtractWithBorrow borrow xs.tail ys.tail).1 then sr.reverse ++ xs
            else normalizeBits ((bit :: df).reverse ++
              (subtractWithBorrow borrow xs.tail ys.tail).2)) [] [] []) =
        divCfg (some .pushQ) ((subtractWithBorrow v.1 xs ys).1, none, none)
          (divWork s (sd.reverse ++ ys)
            (if (subtractWithBorrow v.1 xs ys).1 then sr.reverse ++ xs
              else normalizeBits (df.reverse ++ (subtractWithBorrow v.1 xs ys).2)) [] [] []) := by
      rw [div_subtractWithBorrow_step v.1 xs ys hn]
      simp [bit, borrow, List.reverse_cons, List.append_assoc]
    rw [hout] at he
    apply weakenTime he
    have hl : xs.tail.length + ys.tail.length + 1 ≤ xs.length + ys.length := by
      cases xs <;> cases ys <;> simp_all
      omega
    have hsd : sd'.length ≤ sd.length + 1 := by dsimp [sd']; split <;> simp
    have hsr : sr'.length ≤ sr.length + 1 := by dsimp [sr']; split <;> simp
    simp only [List.length_cons]
    omega
termination_by xs.length + ys.length
decreasing_by
  have hn : xs ≠ [] ∨ ys ≠ [] := by tauto
  cases xs <;> cases ys <;> simp_all
  omega


/-- A clean arithmetic workspace between long-division iterations. -/
def divData (ds ms qs rs : List Bool) : DivData := ⟨ds, ms, qs, rs, [], [], [], []⟩

def divFinal (out : List Bool) : DivData := ⟨[], [], [], [], [], [], [], out⟩

def framePrefix : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: framePrefix bs

@[simp] theorem framePrefix_append (xs ys : List Bool) :
    framePrefix (xs ++ ys) = framePrefix xs ++ framePrefix ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [framePrefix, ih]

@[simp] theorem framePrefix_delimiter (xs ys : List Bool) :
    framePrefix xs ++ false :: ys = Complexity.BitEncoding.frame xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [framePrefix, Complexity.BitEncoding.frame, ih]

@[simp] theorem division_step_delimiter (v : AddState) (s : DivData) :
    divisionMachine.step (divCfg (some .delimiter) v s) =
      some (divCfg (some .reverseQ) v {s with out := false :: s.out}) := by
  simp [divisionMachine, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_outputQ_cons (v : AddState) (s : DivData) (b : Bool)
    (as bs : List Bool) :
    divisionMachine.step (divCfg (some .outputQ) v {s with sd := b :: as, out := bs}) =
      some (divCfg (some .outputQ) (v.1, some b, v.2.2) {s with sd := as, out := true :: b :: bs}) := by
  simp [divisionMachine, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_outputQ_nil (v : AddState) (s : DivData) (bs : List Bool) :
    divisionMachine.step (divCfg (some .outputQ) v {s with sd := [], out := bs}) =
      some (divCfg none (false, none, none) {s with sd := [], out := bs}) := by
  simp [divisionMachine, divCfg, DivData.stacks, step, stepAux]

def division_outputQ (v : AddState) (s : DivData) (as bs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .outputQ) v {s with sd := as, out := bs})
      (some (divCfg none (false, none, none) {s with sd := [], out := framePrefix as.reverse ++ bs}))
      (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep divisionMachine.step (division_step_outputQ_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (as.length + 1) _ _ _
      (oneStep divisionMachine.step (division_step_outputQ_cons v s b as bs))
      (ih (v.1, some b, v.2.2) (true :: b :: bs))
    simpa [List.reverse_cons, framePrefix, List.append_assoc] using h

/-- Serialize the canonical quotient/remainder pair and clear the entire workspace. -/
def division_serialize (v : AddState) (ds qs rs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .clearD) v (divData ds [] qs rs))
      (some (divCfg none (false, none, none) (divFinal (Complexity.BitEncoding.frame qs ++ rs))))
      (ds.length + 2 * rs.length + 2 * qs.length + 6) := by
  let v' : AddState := (v.1, none, v.2.2)
  have hd := division_clearD v (divData ds [] qs rs) ds
  have hr := division_reverseR v' (divData [] [] qs rs) rs []
  have ho := division_outputR v' {divData [] [] qs [] with sr := rs.reverse} rs.reverse []
  have hb := oneStep divisionMachine.step
    (division_step_delimiter v' {divData [] [] qs [] with out := rs})
  have hq := division_reverseQ v' {divData [] [] qs [] with out := false :: rs} qs []
  have hf := division_outputQ v' {divData [] [] [] [] with out := false :: rs} qs.reverse (false :: rs)
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at hr ho hq hf
  have hqf := EvalsToInTime.trans divisionMachine.step (qs.length + 1) (qs.length + 1)
    _ _ _ hq hf
  have hbqf := EvalsToInTime.trans divisionMachine.step 1 ((qs.length + 1) + (qs.length + 1))
    _ _ _ hb hqf
  have hobqf := EvalsToInTime.trans divisionMachine.step (rs.length + 1)
    (((qs.length + 1) + (qs.length + 1)) + 1) _ _ _ ho hbqf
  have hrobqf := EvalsToInTime.trans divisionMachine.step (rs.length + 1)
    ((((qs.length + 1) + (qs.length + 1)) + 1) + (rs.length + 1)) _ _ _ hr hobqf
  have h := EvalsToInTime.trans divisionMachine.step (ds.length + 1)
    (((((qs.length + 1) + (qs.length + 1)) + 1) + (rs.length + 1)) + (rs.length + 1))
    _ _ _ hd hrobqf
  have ht : (((((qs.length + 1) + (qs.length + 1)) + 1) + (rs.length + 1)) +
      (rs.length + 1)) + (ds.length + 1) = ds.length + 2 * rs.length + 2 * qs.length + 6 := by omega
  rw [ht] at h
  simpa [divData, divFinal, framePrefix_delimiter] using h

@[simp] theorem division_step_loop_cons (v : AddState) (b : Bool) (ds ms qs rs : List Bool) :
    divisionMachine.step (divCfg (some .loop) v (divData ds (b :: ms) qs rs)) =
      some (divCfg (some .subtract) (false, none, none)
        (divData ds ms qs (canonicalCons b rs))) := by
  cases rs with
  | nil =>
    cases b <;> simp [divisionMachine, divCanonicalCons, divCfg, divData, DivData.stacks,
      canonicalCons, step, stepAux]
    all_goals funext k; cases k <;> simp [DivData.stacks]
  | cons r rs =>
    cases b <;> simp [divisionMachine, divCanonicalCons, divCfg, divData, DivData.stacks,
      canonicalCons, step, stepAux]
    all_goals funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_loop_nil (v : AddState) (ds qs rs : List Bool) :
    divisionMachine.step (divCfg (some .loop) v (divData ds [] qs rs)) =
      some (divCfg (some .clearD) (v.1, none, v.2.2) (divData ds [] qs rs)) := by
  simp [divisionMachine, divCfg, divData, DivData.stacks, step, stepAux]

@[simp] theorem division_step_pushQ (v : AddState) (ds ms qs rs : List Bool) :
    divisionMachine.step (divCfg (some .pushQ) v (divData ds ms qs rs)) =
      some (divCfg (some .loop) (false, none, none)
        (divData ds ms (canonicalCons (!v.1) qs) rs)) := by
  cases qs with
  | nil =>
    cases hc : v.1 <;> simp [divisionMachine, divCanonicalCons, divCfg, divData, DivData.stacks,
      canonicalCons, step, stepAux, hc]
    all_goals funext k; cases k <;> simp [DivData.stacks]
  | cons q qs =>
    cases hc : v.1 <;> simp [divisionMachine, divCanonicalCons, divCfg, divData, DivData.stacks,
      canonicalCons, step, stepAux, hc]
    all_goals funext k; cases k <;> simp [DivData.stacks]

private theorem division_choose_remainder (xs ds : List Bool) :
    (if (subtractWithBorrow false xs ds).1 then xs
      else normalizeBits (subtractWithBorrow false xs ds).2) =
      (if lessBits xs ds then xs else subBits xs ds) := by
  unfold lessBits subBits
  split <;> simp_all

/-- Long division processes one numerator bit per iteration, with one linear
trial subtraction per bit and a uniformly bounded binary workspace. -/
def division_loop (v : AddState) (ds ms qs rs : List Bool) (B : ℕ)
    (hB : max rs.length ds.length + ms.length ≤ B)
    (hQ : qs.length + ms.length ≤ B) :
    EvalsToInTime divisionMachine.step (divCfg (some .loop) v (divData ds ms qs rs))
      (some (divCfg none (false, none, none)
        (divFinal (Complexity.BitEncoding.frame (divLoop ds ms qs rs).1 ++
          (divLoop ds ms qs rs).2))))
      ((8 * B + 7) * ms.length + 5 * B + 7) := by
  induction ms generalizing v qs rs with
  | nil =>
    have h := EvalsToInTime.trans divisionMachine.step 1
      (ds.length + 2 * rs.length + 2 * qs.length + 6) _ _ _
      (oneStep divisionMachine.step (division_step_loop_nil v ds qs rs))
      (division_serialize (v.1, none, v.2.2) ds qs rs)
    apply weakenTime (by simpa [divLoop] using h)
    simp only [List.length_nil, Nat.add_zero, Nat.mul_zero, Nat.zero_add] at hB hQ ⊢
    omega
  | cons b ms ih =>
    let shifted := canonicalCons b rs
    let underflow := lessBits shifted ds
    let newR := if underflow then shifted else subBits shifted ds
    let newQ := canonicalCons (!underflow) qs
    have hslen := canonicalCons_length_le b rs
    have hqlen := canonicalCons_length_le (!underflow) qs
    have hrlen : newR.length ≤ max rs.length ds.length + 1 := by
      dsimp [newR]
      cases hu : underflow
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have h := subBits_length_le shifted ds
        dsimp [shifted] at h ⊢
        omega
      · simp only [↓reduceIte]
        dsimp [shifted]
        omega
    have hB' : max newR.length ds.length + ms.length ≤ B := by
      simp only [List.length_cons] at hB
      omega
    have hQ' : newQ.length + ms.length ≤ B := by
      simp only [List.length_cons] at hQ
      dsimp [newQ]
      omega
    have hsub0 := division_subtract (false, none, none) (divData ds ms qs shifted)
      shifted ds [] [] []
    have hsub : EvalsToInTime divisionMachine.step
        (divCfg (some .subtract) (false, none, none) (divData ds ms qs shifted))
        (some (divCfg (some .pushQ) (underflow, none, none) (divData ds ms qs newR)))
        (4 * (shifted.length + ds.length) + 5) := by
      simpa [divWork, divData, List.reverse_nil, division_choose_remainder, underflow, newR]
        using hsub0
    have hpush := oneStep divisionMachine.step
      (division_step_pushQ (underflow, none, none) ds ms qs newR)
    have hi := ih (false, none, none) newQ newR hB' hQ'
    have hpi := EvalsToInTime.trans divisionMachine.step 1
      ((8 * B + 7) * ms.length + 5 * B + 7) _ _ _ hpush hi
    have hspi := EvalsToInTime.trans divisionMachine.step
      (4 * (shifted.length + ds.length) + 5)
      (((8 * B + 7) * ms.length + 5 * B + 7) + 1) _ _ _ hsub hpi
    have h := EvalsToInTime.trans divisionMachine.step 1
      ((((8 * B + 7) * ms.length + 5 * B + 7) + 1) +
        (4 * (shifted.length + ds.length) + 5)) _ _ _
      (oneStep divisionMachine.step (division_step_loop_cons v b ds ms qs rs)) hspi
    apply weakenTime (by simpa [divLoop, newQ, newR, shifted, underflow] using h)
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hB hQ ⊢
    omega


@[simp] theorem division_step_parse_bit (v : AddState) (s : DivData) (b : Bool)
    (ns ms : List Bool) :
    divisionMachine.step (divCfg (some .parse) v {s with ds := true :: b :: ns, ms := ms}) =
      some (divCfg (some .parse) (v.1, some b, v.2.2) {s with ds := ns, ms := b :: ms}) := by
  simp [divisionMachine, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

@[simp] theorem division_step_parse_end (v : AddState) (s : DivData) (ds ms : List Bool) :
    divisionMachine.step (divCfg (some .parse) v {s with ds := false :: ds, ms := ms}) =
      some (divCfg (some .check) (v.1, some false, v.2.2) {s with ds := ds, ms := ms}) := by
  simp [divisionMachine, divCfg, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

/-- The parser reverses the numerator, ready for most-significant-first processing. -/
def division_parse (v : AddState) (s : DivData) (xs ds ms : List Bool) :
    EvalsToInTime divisionMachine.step
      (divCfg (some .parse) v {s with ds := Complexity.BitEncoding.frame xs ++ ds, ms := ms})
      (some (divCfg (some .check) (v.1, some false, v.2.2)
        {s with ds := ds, ms := xs.reverse ++ ms})) (xs.length + 1) := by
  induction xs generalizing v ms with
  | nil => simpa [Complexity.BitEncoding.frame] using
      oneStep divisionMachine.step (division_step_parse_end v s ds ms)
  | cons b xs ih =>
    have h := EvalsToInTime.trans divisionMachine.step 1 (xs.length + 1) _ _ _
      (oneStep divisionMachine.step
        (division_step_parse_bit v s b (Complexity.BitEncoding.frame xs ++ ds) ms))
      (ih (v.1, some b, v.2.2) (b :: ms))
    simpa [Complexity.BitEncoding.frame, List.reverse_cons, List.append_assoc] using h

@[simp] theorem division_step_check_cons (v : AddState) (b : Bool) (ds ms qs rs : List Bool) :
    divisionMachine.step (divCfg (some .check) v (divData (b :: ds) ms qs rs)) =
      some (divCfg (some .loop) (false, none, none) (divData (b :: ds) ms qs rs)) := by
  simp [divisionMachine, divCfg, divData, DivData.stacks, step, stepAux]

@[simp] theorem division_step_check_nil (v : AddState) (ms : List Bool) :
    divisionMachine.step (divCfg (some .check) v (divData [] ms [] [])) =
      some (divCfg (some .zeroCopy) (v.1, none, v.2.2) (divData [] ms [] [])) := by
  simp [divisionMachine, divCfg, divData, DivData.stacks, step, stepAux]

@[simp] theorem division_step_zeroFinish (v : AddState) (xs : List Bool) :
    divisionMachine.step (divCfg (some .zeroFinish) v (divFinal xs)) =
      some (divCfg none (false, none, none) (divFinal (false :: xs))) := by
  simp [divisionMachine, divCfg, divFinal, DivData.stacks, step, stepAux]
  funext k; cases k <;> simp [DivData.stacks]

/-- Division by zero returns quotient zero and the original input as remainder. -/
def division_zero (v : AddState) (xs : List Bool) :
    EvalsToInTime divisionMachine.step (divCfg (some .check) v (divData [] xs.reverse [] []))
      (some (divCfg none (false, none, none) (divFinal (false :: xs)))) (xs.length + 3) := by
  have hc := oneStep divisionMachine.step (division_step_check_nil v xs.reverse)
  have hz := division_zeroCopy (v.1, none, v.2.2) (divData [] [] [] []) xs.reverse []
  have hf := oneStep divisionMachine.step
    (division_step_zeroFinish (v.1, none, v.2.2) xs)
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at hz
  have hzf := EvalsToInTime.trans divisionMachine.step (xs.length + 1) 1 _ _ _ hz hf
  have h := EvalsToInTime.trans divisionMachine.step 1 (1 + (xs.length + 1)) _ _ _ hc hzf
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The complete serialized input/output computation is polynomial in bit length,
including long division, divisor-zero behavior, output framing, and cleanup. -/
def division_outputs (xs ds : List Bool) :
    TM2OutputsInTime divisionMachine (Complexity.BitEncoding.frame xs ++ ds)
      (some (Complexity.BitEncoding.frame (divBits xs ds).1 ++ (divBits xs ds).2))
      ((8 * (Complexity.BitEncoding.frame xs ++ ds).length + 7) *
        (Complexity.BitEncoding.frame xs ++ ds).length +
        6 * (Complexity.BitEncoding.frame xs ++ ds).length + 9) := by
  have hp := division_parse (false, none, none) (divData [] [] [] []) xs ds []
  simp only [List.append_nil] at hp
  have hi : initList divisionMachine (Complexity.BitEncoding.frame xs ++ ds) =
      divCfg (some .parse) (false, none, none) (divData (Complexity.BitEncoding.frame xs ++ ds) [] [] []) := by
    unfold initList divCfg divData
    congr 1
    funext k; cases k <;> rfl
  have ho (out : List Bool) : haltList divisionMachine out =
      divCfg none (false, none, none) (divFinal out) := by
    unfold haltList divCfg divFinal
    congr 1
    funext k; cases k <;> rfl
  unfold TM2OutputsInTime
  simp only [Option.map_some, hi, ho]
  cases ds with
  | nil =>
    have hz := division_zero (false, some false, none) xs
    have h := EvalsToInTime.trans divisionMachine.step (xs.length + 1) (xs.length + 3)
      _ _ _ hp hz
    apply weakenTime (by simpa [divBits, Complexity.BitEncoding.frame] using h)
    simp only [List.append_nil, Complexity.BitEncoding.frame_length]
    omega
  | cons d ds =>
    let B := xs.length + (d :: ds).length
    have hl := division_loop (false, none, none) (d :: ds) xs.reverse [] [] B
      (by simp [B, Nat.add_comm]) (by simp [B])
    simp only [List.length_reverse] at hl
    have hc := oneStep divisionMachine.step
      (division_step_check_cons (false, some false, none) d ds xs.reverse [] [])
    have hcl := EvalsToInTime.trans divisionMachine.step 1
      ((8 * B + 7) * xs.length + 5 * B + 7) _ _ _ hc hl
    have h := EvalsToInTime.trans divisionMachine.step (xs.length + 1)
      (((8 * B + 7) * xs.length + 5 * B + 7) + 1) _ _ _ hp hcl
    apply weakenTime (by simpa [divBits] using h)
    simp only [List.length_append, Complexity.BitEncoding.frame_length]
    have hB : B ≤ 2 * xs.length + 1 + (d :: ds).length := by dsimp [B]; omega
    have hn : xs.length ≤ 2 * xs.length + 1 + (d :: ds).length := by omega
    have hm : (8 * B + 7) * xs.length ≤
        (8 * (2 * xs.length + 1 + (d :: ds).length) + 7) *
          (2 * xs.length + 1 + (d :: ds).length) := Nat.mul_le_mul (by omega) hn
    omega

/-- Exact canonical quotient and remainder in quadratic binary time. -/
noncomputable def divisionComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat).toFinEncoding
      (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat).toFinEncoding
      (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2)) where
  tm := divisionMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := (Polynomial.C 8 * Polynomial.X + Polynomial.C 7) * Polynomial.X +
    Polynomial.C 6 * Polynomial.X + Polynomial.C 9
  outputsFun p := by
    have h := division_outputs (Computability.encodeNat p.1) (Computability.encodeNat p.2)
    rw [divBits_encodeNat] at h
    simpa [Complexity.BitEncoding.nat, Complexity.BitEncoding.prod,
      Complexity.BitEncoding.toFinEncoding, Polynomial.eval_add, Polynomial.eval_mul,
      Equiv.refl, Equiv.symm] using h

theorem fp_division :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat)
      (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat)
      (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2)) := ⟨divisionComputable⟩

end PlanarHom.BinaryArithmetic
