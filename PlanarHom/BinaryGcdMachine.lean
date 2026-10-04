import PlanarHom.BinaryGcdBits
import PlanarHom.BinaryDivisionMachine
import PlanarHom.BitMachineSubroutine

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-! # Euclidean gcd with an explicitly embedded binary long-division subroutine -/
namespace PlanarHom.BinaryArithmetic
open Turing Turing.TM2
open PlanarHom.MachineComposition PlanarHom.BitMachineSubroutine

inductive GcdStack | a | b | t | u deriving DecidableEq, Fintype
inductive GcdLabel
  | parseInput | restoreA | check | copyB | restoreB | copyInput | delimiter | reverseA | frameA
  | returned | moveB | newA | moveR | newB | finishReverse | finishOutput
  deriving DecidableEq, Fintype

structure GcdData where
  a : List Bool
  b : List Bool
  t : List Bool
  u : List Bool

def GcdData.stacks (s : GcdData) : GcdStack → List Bool
  | .a => s.a | .b => s.b | .t => s.t | .u => s.u

abbrev GcdStmt := Stmt (fun _ : GcdStack ⊕ DivStack => Bool) (GcdLabel ⊕ DivLabel) (AddState × Unit)

def gcdPop (k : GcdStack ⊕ DivStack) (q : GcdStmt) : GcdStmt :=
  .pop k (fun _ b => ((false, b, none), ())) q

def gcdMove (src dst : GcdStack ⊕ DivStack) (again next : GcdLabel) : GcdStmt :=
  gcdPop src <| .branch (fun v => v.1.2.1.isSome)
    (.push dst (fun v => v.1.2.1.getD false) (.goto (fun _ => .inl again)))
    (.goto (fun _ => .inl next))

def gcdOuterProgram : GcdLabel → GcdStmt
  | .parseInput => gcdPop (.inl .b) <|
        .branch (fun v => v.1.2.1.getD false)
          (gcdPop (.inl .b) <|
            .push (.inl .t) (fun v => v.1.2.1.getD false) (.goto (fun _ => .inl .parseInput)))
          (.goto (fun _ => .inl .restoreA))
  | .restoreA => gcdMove (.inl .t) (.inl .a) .restoreA .check
  | .check => .peek (.inl .b) (fun _ b => ((false, b, none), ())) <|
        .branch (fun v => v.1.2.1.isSome)
          (.goto (fun _ => .inl .copyB)) (.goto (fun _ => .inl .finishReverse))
  | .copyB => gcdPop (.inl .b) <|
        .branch (fun v => v.1.2.1.isSome)
          (.push (.inl .t) (fun v => v.1.2.1.getD false) <|
            .push (.inl .u) (fun v => v.1.2.1.getD false) (.goto (fun _ => .inl .copyB)))
          (.goto (fun _ => .inl .restoreB))
  | .restoreB => gcdMove (.inl .t) (.inl .b) .restoreB .copyInput
  | .copyInput => gcdMove (.inl .u) (.inr .ds) .copyInput .delimiter
  | .delimiter => .push (.inr .ds) (fun _ => false) (.goto (fun _ => .inl .reverseA))
  | .reverseA => gcdMove (.inl .a) (.inl .t) .reverseA .frameA
  | .frameA => gcdPop (.inl .t) <|
        .branch (fun v => v.1.2.1.isSome)
          (.push (.inr .ds) (fun v => v.1.2.1.getD false) <|
            .push (.inr .ds) (fun _ => true) (.goto (fun _ => .inl .frameA)))
          (.goto (fun _ => .inr .parse))
  | .returned => gcdPop (.inr .out) <|
        .branch (fun v => v.1.2.1.getD false)
          (gcdPop (.inr .out) (.goto (fun _ => .inl .returned)))
          (.goto (fun _ => .inl .moveB))
  | .moveB => gcdMove (.inl .b) (.inl .t) .moveB .newA
  | .newA => gcdMove (.inl .t) (.inl .a) .newA .moveR
  | .moveR => gcdMove (.inr .out) (.inl .t) .moveR .newB
  | .newB => gcdMove (.inl .t) (.inl .b) .newB .check
  | .finishReverse => gcdMove (.inl .a) (.inl .t) .finishReverse .finishOutput
  | .finishOutput => gcdPop (.inl .t) <|
        .branch (fun v => v.1.2.1.isSome)
          (.push (.inr .out) (fun v => v.1.2.1.getD false) (.goto (fun _ => .inl .finishOutput)))
          .halt

/-- The right-hand stack bank and labels contain the literal compiled division
program. The left-hand bank retains the Euclidean denominator across each call. -/
def gcdMachine : FinTM2 where
  K := GcdStack ⊕ DivStack
  k₀ := .inl .b
  k₁ := .inr .out
  Γ _ := Bool
  Λ := GcdLabel ⊕ DivLabel
  main := .inl .parseInput
  σ := AddState × Unit
  initialState := ((false, none, none), ())
  m := Sum.elim gcdOuterProgram (fun l => redirectHalt (.inl .returned)
    (liftStmt (bankEmbedding GcdStack DivStack) Sum.inr (divisionMachine.m l)))

@[simp] theorem gcdMachine_m_inl (l : GcdLabel) :
    gcdMachine.m (.inl l) = gcdOuterProgram l := rfl


@[simp] theorem gcd_inl_inj (j k : GcdStack) :
    @Eq gcdMachine.K (Sum.inl j) (Sum.inl k) ↔ j = k :=
  ⟨Sum.inl.inj, congrArg Sum.inl⟩

@[simp] theorem gcd_inr_inj (j k : DivStack) :
    @Eq gcdMachine.K (Sum.inr j) (Sum.inr k) ↔ j = k :=
  ⟨Sum.inr.inj, congrArg Sum.inr⟩

def gcdCfg (l : Option (GcdLabel ⊕ DivLabel)) (v : AddState) (s : GcdData) (d : DivData) :
    gcdMachine.Cfg := ⟨l, (v, ()), Sum.elim s.stacks d.stacks⟩

def gcdData (a b : List Bool) : GcdData := ⟨a, b, [], []⟩
def emptyDivData : DivData := divData [] [] [] []

/-- The source halt is represented by the return label, with caller-owned words
retained literally in their separate bank. -/
def gcdBankCfg (s : GcdData) (c : divisionMachine.Cfg) : gcdMachine.Cfg :=
  continueCfg (.inl .returned) (bankCfg s.stacks c)

theorem gcd_bank_step (s : GcdData) (c c' : divisionMachine.Cfg)
    (h : divisionMachine.step c = some c') :
    gcdMachine.step (gcdBankCfg s c) = some (gcdBankCfg s c') := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => simp [FinTM2.step, step] at h
  | some l =>
    simp only [FinTM2.step, step, Option.some.injEq] at h
    subst c'
    change some (stepAux _ _ _) = some _
    congr 1
    exact bankStmt_return_correct s.stacks GcdLabel.returned (divisionMachine.m l) v S

/-- Exact-time simulation of a complete real division run inside the gcd program. -/
def gcd_division_call (s : GcdData) (a b : List Bool) :
    EvalsToInTime gcdMachine.step
      (gcdBankCfg s (initList divisionMachine (Complexity.BitEncoding.frame a ++ b)))
      (some (gcdBankCfg s (haltList divisionMachine
        (Complexity.BitEncoding.frame (divBits a b).1 ++ (divBits a b).2))))
      ((8 * (Complexity.BitEncoding.frame a ++ b).length + 7) *
        (Complexity.BitEncoding.frame a ++ b).length +
        6 * (Complexity.BitEncoding.frame a ++ b).length + 9) := by
  let h := division_outputs a b
  refine ⟨⟨h.steps, ?_⟩, h.steps_le_m⟩
  obtain ⟨c, hc, he⟩ := simulate_iterations divisionMachine.step gcdMachine.step
    (fun x y => y = gcdBankCfg s x)
    (by intro x x' y hs hy; subst y; exact ⟨_, gcd_bank_step s x x' hs, rfl⟩)
    _ _ _ h.steps h.evals_in_steps rfl
  simpa [he] using hc

@[simp] theorem gcd_step_restoreA_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .restoreA)) v {s with t := b :: as, a := bs} d) =
      some (gcdCfg (some (.inl .restoreA)) (false, some b, none) {s with t := as, a := b :: bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_restoreA_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .restoreA)) v {s with t := [], a := bs} d) =
      some (gcdCfg (some (.inl .check)) (false, none, none) {s with t := [], a := bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]

def gcd_restoreA (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .restoreA)) v {s with t := as, a := bs} d)
      (some (gcdCfg (some (.inl .check)) (false, none, none) {s with t := [], a := as.reverse ++ bs} d)) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_restoreA_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_restoreA_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_restoreB_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .restoreB)) v {s with t := b :: as, b := bs} d) =
      some (gcdCfg (some (.inl .restoreB)) (false, some b, none) {s with t := as, b := b :: bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_restoreB_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .restoreB)) v {s with t := [], b := bs} d) =
      some (gcdCfg (some (.inl .copyInput)) (false, none, none) {s with t := [], b := bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]

def gcd_restoreB (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .restoreB)) v {s with t := as, b := bs} d)
      (some (gcdCfg (some (.inl .copyInput)) (false, none, none) {s with t := [], b := as.reverse ++ bs} d)) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_restoreB_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_restoreB_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_copyInput_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .copyInput)) v {s with u := b :: as} {d with ds := bs}) =
      some (gcdCfg (some (.inl .copyInput)) (false, some b, none) {s with u := as} {d with ds := b :: bs}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, DivData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj, gcd_inr_inj]

@[simp] theorem gcd_step_copyInput_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .copyInput)) v {s with u := []} {d with ds := bs}) =
      some (gcdCfg (some (.inl .delimiter)) (false, none, none) {s with u := []} {d with ds := bs}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, DivData.stacks, step, stepAux]

def gcd_copyInput (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .copyInput)) v {s with u := as} {d with ds := bs})
      (some (gcdCfg (some (.inl .delimiter)) (false, none, none) {s with u := []} {d with ds := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_copyInput_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_copyInput_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_reverseA_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .reverseA)) v {s with a := b :: as, t := bs} d) =
      some (gcdCfg (some (.inl .reverseA)) (false, some b, none) {s with a := as, t := b :: bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_reverseA_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .reverseA)) v {s with a := [], t := bs} d) =
      some (gcdCfg (some (.inl .frameA)) (false, none, none) {s with a := [], t := bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]

def gcd_reverseA (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .reverseA)) v {s with a := as, t := bs} d)
      (some (gcdCfg (some (.inl .frameA)) (false, none, none) {s with a := [], t := as.reverse ++ bs} d)) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_reverseA_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_reverseA_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_moveB_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .moveB)) v {s with b := b :: as, t := bs} d) =
      some (gcdCfg (some (.inl .moveB)) (false, some b, none) {s with b := as, t := b :: bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_moveB_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .moveB)) v {s with b := [], t := bs} d) =
      some (gcdCfg (some (.inl .newA)) (false, none, none) {s with b := [], t := bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]

def gcd_moveB (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .moveB)) v {s with b := as, t := bs} d)
      (some (gcdCfg (some (.inl .newA)) (false, none, none) {s with b := [], t := as.reverse ++ bs} d)) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_moveB_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_moveB_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_newA_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .newA)) v {s with t := b :: as, a := bs} d) =
      some (gcdCfg (some (.inl .newA)) (false, some b, none) {s with t := as, a := b :: bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_newA_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .newA)) v {s with t := [], a := bs} d) =
      some (gcdCfg (some (.inl .moveR)) (false, none, none) {s with t := [], a := bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]

def gcd_newA (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .newA)) v {s with t := as, a := bs} d)
      (some (gcdCfg (some (.inl .moveR)) (false, none, none) {s with t := [], a := as.reverse ++ bs} d)) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_newA_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_newA_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_moveR_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .moveR)) v {s with t := bs} {d with out := b :: as}) =
      some (gcdCfg (some (.inl .moveR)) (false, some b, none) {s with t := b :: bs} {d with out := as}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, DivData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj, gcd_inr_inj]

@[simp] theorem gcd_step_moveR_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .moveR)) v {s with t := bs} {d with out := []}) =
      some (gcdCfg (some (.inl .newB)) (false, none, none) {s with t := bs} {d with out := []}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, DivData.stacks, step, stepAux]

def gcd_moveR (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .moveR)) v {s with t := bs} {d with out := as})
      (some (gcdCfg (some (.inl .newB)) (false, none, none) {s with t := as.reverse ++ bs} {d with out := []})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_moveR_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_moveR_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_newB_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .newB)) v {s with t := b :: as, b := bs} d) =
      some (gcdCfg (some (.inl .newB)) (false, some b, none) {s with t := as, b := b :: bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_newB_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .newB)) v {s with t := [], b := bs} d) =
      some (gcdCfg (some (.inl .check)) (false, none, none) {s with t := [], b := bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]

def gcd_newB (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .newB)) v {s with t := as, b := bs} d)
      (some (gcdCfg (some (.inl .check)) (false, none, none) {s with t := [], b := as.reverse ++ bs} d)) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_newB_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_newB_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_finishReverse_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .finishReverse)) v {s with a := b :: as, t := bs} d) =
      some (gcdCfg (some (.inl .finishReverse)) (false, some b, none) {s with a := as, t := b :: bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_finishReverse_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .finishReverse)) v {s with a := [], t := bs} d) =
      some (gcdCfg (some (.inl .finishOutput)) (false, none, none) {s with a := [], t := bs} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdMove, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]

def gcd_finishReverse (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .finishReverse)) v {s with a := as, t := bs} d)
      (some (gcdCfg (some (.inl .finishOutput)) (false, none, none) {s with a := [], t := as.reverse ++ bs} d)) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_finishReverse_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_finishReverse_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_finishOutput_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .finishOutput)) v {s with t := b :: as} {d with out := bs}) =
      some (gcdCfg (some (.inl .finishOutput)) (false, some b, none) {s with t := as} {d with out := b :: bs}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, GcdData.stacks, DivData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj, gcd_inr_inj]

@[simp] theorem gcd_step_finishOutput_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .finishOutput)) v {s with t := []} {d with out := bs}) =
      some (gcdCfg none (false, none, none) {s with t := []} {d with out := bs}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, GcdData.stacks, DivData.stacks, step, stepAux]

def gcd_finishOutput (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .finishOutput)) v {s with t := as} {d with out := bs})
      (some (gcdCfg none (false, none, none) {s with t := []} {d with out := as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_finishOutput_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_finishOutput_cons v s d b as bs))
      (ih (false, some b, none) (b :: bs))
    simpa [List.reverse_cons, List.append_assoc] using h


@[simp] theorem gcd_step_copyB_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (bs ts us : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .copyB)) v {s with b := b :: bs, t := ts, u := us} d) =
      some (gcdCfg (some (.inl .copyB)) (false, some b, none)
        {s with b := bs, t := b :: ts, u := b :: us} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_copyB_nil (v : AddState) (s : GcdData) (d : DivData) (ts us : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .copyB)) v {s with b := [], t := ts, u := us} d) =
      some (gcdCfg (some (.inl .restoreB)) (false, none, none) {s with b := [], t := ts, u := us} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]

def gcd_copyB (v : AddState) (s : GcdData) (d : DivData) (bs ts us : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .copyB)) v {s with b := bs, t := ts, u := us} d)
      (some (gcdCfg (some (.inl .restoreB)) (false, none, none)
        {s with b := [], t := bs.reverse ++ ts, u := bs.reverse ++ us} d)) (bs.length + 1) := by
  induction bs generalizing v ts us with
  | nil => simpa using oneStep gcdMachine.step (gcd_step_copyB_nil v s d ts us)
  | cons b bs ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (bs.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_copyB_cons v s d b bs ts us))
      (ih (false, some b, none) (b :: ts) (b :: us))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem gcd_step_delimiter (v : AddState) (s : GcdData) (d : DivData) :
    gcdMachine.step (gcdCfg (some (.inl .delimiter)) v s d) =
      some (gcdCfg (some (.inl .reverseA)) v s {d with ds := false :: d.ds}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdCfg, DivData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inr_inj]

@[simp] theorem gcd_step_frameA_cons (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (as bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .frameA)) v {s with t := b :: as} {d with ds := bs}) =
      some (gcdCfg (some (.inl .frameA)) (false, some b, none) {s with t := as}
        {d with ds := true :: b :: bs}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, GcdData.stacks, DivData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj, gcd_inr_inj]

@[simp] theorem gcd_step_frameA_nil (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .frameA)) v {s with t := []} {d with ds := bs}) =
      some (gcdCfg (some (.inr .parse)) (false, none, none) {s with t := []} {d with ds := bs}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, GcdData.stacks, DivData.stacks, step, stepAux]

def gcd_frameA (v : AddState) (s : GcdData) (d : DivData) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .frameA)) v {s with t := as} {d with ds := bs})
      (some (gcdCfg (some (.inr .parse)) (false, none, none) {s with t := []}
        {d with ds := framePrefix as.reverse ++ bs})) (as.length + 1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep gcdMachine.step (gcd_step_frameA_nil v s d bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_frameA_cons v s d b as bs))
      (ih (false, some b, none) (true :: b :: bs))
    simpa [List.reverse_cons, framePrefix, List.append_assoc] using h

/-- Prepare a literal binary division input while preserving the denominator in
the caller's separate stack bank. -/
def gcd_prepare (v : AddState) (as bs : List Bool) :
    EvalsToInTime gcdMachine.step
      (gcdCfg (some (.inl .copyB)) v (gcdData as bs) emptyDivData)
      (some (gcdCfg (some (.inr .parse)) (false, none, none) (gcdData [] bs)
        {emptyDivData with ds := Complexity.BitEncoding.frame as ++ bs}))
      (2 * as.length + 3 * bs.length + 6) := by
  have h1 := gcd_copyB v (gcdData as bs) emptyDivData bs [] []
  have h2 := gcd_restoreB (false, none, none) {gcdData as [] with u := bs.reverse}
    emptyDivData bs.reverse []
  have h3 := gcd_copyInput (false, none, none) (gcdData as bs) emptyDivData bs.reverse []
  have h4 := oneStep gcdMachine.step
    (gcd_step_delimiter (false, none, none) (gcdData as bs) {emptyDivData with ds := bs})
  have h5 := gcd_reverseA (false, none, none) (gcdData as bs)
    {emptyDivData with ds := false :: bs} as []
  have h6 := gcd_frameA (false, none, none) (gcdData [] bs) emptyDivData as.reverse (false :: bs)
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at h1 h2 h3 h5 h6
  have h56 := EvalsToInTime.trans gcdMachine.step (as.length + 1) (as.length + 1) _ _ _ h5 h6
  have h456 := EvalsToInTime.trans gcdMachine.step 1 ((as.length + 1) + (as.length + 1)) _ _ _ h4 h56
  have h3456 := EvalsToInTime.trans gcdMachine.step (bs.length + 1)
    (((as.length + 1) + (as.length + 1)) + 1) _ _ _ h3 h456
  have h23456 := EvalsToInTime.trans gcdMachine.step (bs.length + 1)
    ((((as.length + 1) + (as.length + 1)) + 1) + (bs.length + 1)) _ _ _ h2 h3456
  have h := EvalsToInTime.trans gcdMachine.step (bs.length + 1)
    (((((as.length + 1) + (as.length + 1)) + 1) + (bs.length + 1)) + (bs.length + 1)) _ _ _ h1 h23456
  have ht : (((((as.length + 1) + (as.length + 1)) + 1) + (bs.length + 1)) +
      (bs.length + 1)) + (bs.length + 1) = 2 * as.length + 3 * bs.length + 6 := by omega
  rw [ht] at h
  simpa [gcdData, framePrefix_delimiter] using h

@[simp] theorem gcd_step_returned_bit (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .returned)) v s {d with out := true :: b :: bs}) =
      some (gcdCfg (some (.inl .returned)) (false, some b, none) s {d with out := bs}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, DivData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inr_inj]

@[simp] theorem gcd_step_returned_end (v : AddState) (s : GcdData) (d : DivData) (bs : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .returned)) v s {d with out := false :: bs}) =
      some (gcdCfg (some (.inl .moveB)) (false, some false, none) s {d with out := bs}) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, DivData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inr_inj]

def gcd_discard_quotient (v : AddState) (s : GcdData) (d : DivData) (qs rs : List Bool) :
    EvalsToInTime gcdMachine.step
      (gcdCfg (some (.inl .returned)) v s {d with out := Complexity.BitEncoding.frame qs ++ rs})
      (some (gcdCfg (some (.inl .moveB)) (false, some false, none) s {d with out := rs}))
      (qs.length + 1) := by
  induction qs generalizing v with
  | nil => simpa [Complexity.BitEncoding.frame] using
      oneStep gcdMachine.step (gcd_step_returned_end v s d rs)
  | cons b qs ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (qs.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_returned_bit v s d b (Complexity.BitEncoding.frame qs ++ rs)))
      (ih (false, some b, none))
    simpa [Complexity.BitEncoding.frame] using h

/-- Consume the subroutine result and install the next Euclidean pair `(b,r)`. -/
def gcd_return (v : AddState) (bs qs rs : List Bool) :
    EvalsToInTime gcdMachine.step
      (gcdCfg (some (.inl .returned)) v (gcdData [] bs)
        (divFinal (Complexity.BitEncoding.frame qs ++ rs)))
      (some (gcdCfg (some (.inl .check)) (false, none, none) (gcdData bs rs) emptyDivData))
      (qs.length + 2 * bs.length + 2 * rs.length + 5) := by
  have h1 := gcd_discard_quotient v (gcdData [] bs) emptyDivData qs rs
  have h2 := gcd_moveB (false, some false, none) (gcdData [] bs) (divFinal rs) bs []
  have h3 := gcd_newA (false, none, none) (gcdData [] []) (divFinal rs) bs.reverse []
  have h4 := gcd_moveR (false, none, none) (gcdData bs []) emptyDivData rs []
  have h5 := gcd_newB (false, none, none) (gcdData bs []) emptyDivData rs.reverse []
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at h2 h3 h4 h5
  have h45 := EvalsToInTime.trans gcdMachine.step (rs.length + 1) (rs.length + 1) _ _ _ h4 h5
  have h345 := EvalsToInTime.trans gcdMachine.step (bs.length + 1)
    ((rs.length + 1) + (rs.length + 1)) _ _ _ h3 h45
  have h2345 := EvalsToInTime.trans gcdMachine.step (bs.length + 1)
    (((rs.length + 1) + (rs.length + 1)) + (bs.length + 1)) _ _ _ h2 h345
  have h := EvalsToInTime.trans gcdMachine.step (qs.length + 1)
    ((((rs.length + 1) + (rs.length + 1)) + (bs.length + 1)) + (bs.length + 1)) _ _ _ h1 h2345
  have ht : ((((rs.length + 1) + (rs.length + 1)) + (bs.length + 1)) +
      (bs.length + 1)) + (qs.length + 1) = qs.length + 2 * bs.length + 2 * rs.length + 5 := by omega
  rw [ht] at h
  exact h


@[simp] theorem gcdBankCfg_initial (s : GcdData) (xs : List Bool) :
    gcdBankCfg s (initList divisionMachine xs) =
      gcdCfg (some (.inr .parse)) (false, none, none) s {emptyDivData with ds := xs} := by
  unfold gcdBankCfg continueCfg bankCfg initList gcdCfg
  congr 1
  funext k; rcases k with k | k
  · rfl
  · cases k <;> rfl

@[simp] theorem gcdBankCfg_halt (s : GcdData) (xs : List Bool) :
    gcdBankCfg s (haltList divisionMachine xs) =
      gcdCfg (some (.inl .returned)) (false, none, none) s (divFinal xs) := by
  unfold gcdBankCfg continueCfg bankCfg haltList gcdCfg
  congr 1
  funext k; rcases k with k | k
  · rfl
  · cases k <;> rfl

@[simp] theorem gcd_step_check_nil (v : AddState) (as : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .check)) v (gcdData as []) emptyDivData) =
      some (gcdCfg (some (.inl .finishReverse)) (false, none, none) (gcdData as []) emptyDivData) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdCfg, gcdData, GcdData.stacks, step, stepAux]

@[simp] theorem gcd_step_check_nonempty (v : AddState) (as bs : List Bool) (hb : bs ≠ []) :
    gcdMachine.step (gcdCfg (some (.inl .check)) v (gcdData as bs) emptyDivData) =
      some (gcdCfg (some (.inl .copyB)) (false, bs.head?, none) (gcdData as bs) emptyDivData) := by
  cases bs with
  | nil => contradiction
  | cons b bs => simp [gcdMachine_m_inl, gcdOuterProgram, gcdCfg, gcdData, GcdData.stacks, step, stepAux]

/-- The terminal Euclidean case returns its first operand and clears both banks. -/
def gcd_stop (v : AddState) (as : List Bool) :
    EvalsToInTime gcdMachine.step (gcdCfg (some (.inl .check)) v (gcdData as []) emptyDivData)
      (some (gcdCfg none (false, none, none) (gcdData [] []) (divFinal as)))
      (2 * as.length + 3) := by
  have h1 := oneStep gcdMachine.step (gcd_step_check_nil v as)
  have h2 := gcd_finishReverse (false, none, none) (gcdData as []) emptyDivData as []
  have h3 := gcd_finishOutput (false, none, none) (gcdData [] []) emptyDivData as.reverse []
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at h2 h3
  have h23 := EvalsToInTime.trans gcdMachine.step (as.length + 1) (as.length + 1) _ _ _ h2 h3
  have h := EvalsToInTime.trans gcdMachine.step 1 ((as.length + 1) + (as.length + 1)) _ _ _ h1 h23
  have ht : ((as.length + 1) + (as.length + 1)) + 1 = 2 * as.length + 3 := by omega
  rw [ht] at h
  exact h

/-- A uniform bound for one Euclidean division-and-install iteration when each
operand word has at most `n` bits. -/
def gcdStepTime (n : ℕ) : ℕ :=
  (8 * (3*n+1) + 7) * (3*n+1) + 6 * (3*n+1) + 9 + 10*n + 12

/-- A genuine Euclidean update uses the exact proved long-division program,
including explicit input serialization and result parsing. -/
def gcd_euclid_run (v : AddState) (a b L : ℕ) (hb : 0 < b)
    (haL : (Computability.encodeNat a).length ≤ L)
    (hbL : (Computability.encodeNat b).length ≤ L) :
    EvalsToInTime gcdMachine.step
      (gcdCfg (some (.inl .check)) v (gcdData (Computability.encodeNat a) (Computability.encodeNat b)) emptyDivData)
      (some (gcdCfg (some (.inl .check)) (false, none, none)
        (gcdData (Computability.encodeNat b) (Computability.encodeNat (a%b))) emptyDivData))
      (gcdStepTime L) := by
  let as := Computability.encodeNat a
  let bs := Computability.encodeNat b
  let qs := Computability.encodeNat (a/b)
  let rs := Computability.encodeNat (a%b)
  let t := (Complexity.BitEncoding.frame as ++ bs).length
  have hne : bs ≠ [] := by simpa [bs] using (show b ≠ 0 by omega)
  have h1 := oneStep gcdMachine.step (gcd_step_check_nonempty v as bs hne)
  have h2 := gcd_prepare (false, bs.head?, none) as bs
  have h3 := gcd_division_call (gcdData [] bs) as bs
  simp only [gcdBankCfg_initial, gcdBankCfg_halt, as, bs, divBits_encodeNat] at h3
  have h4 := gcd_return (false, none, none) bs qs rs
  have h34 := EvalsToInTime.trans gcdMachine.step ((8*t+7)*t+6*t+9)
    (qs.length + 2*bs.length + 2*rs.length + 5) _ _ _ h3 h4
  have h234 := EvalsToInTime.trans gcdMachine.step (2*as.length+3*bs.length+6)
    ((qs.length + 2*bs.length + 2*rs.length + 5) + ((8*t+7)*t+6*t+9)) _ _ _ h2 h34
  have h := EvalsToInTime.trans gcdMachine.step 1
    (((qs.length + 2*bs.length + 2*rs.length + 5) + ((8*t+7)*t+6*t+9)) +
      (2*as.length+3*bs.length+6)) _ _ _ h1 h234
  apply weakenTime h
  have hq := encodeNat_length_mono (Nat.div_le_self a b)
  have hr := encodeNat_length_mono (Nat.le_of_lt (Nat.mod_lt a hb))
  change qs.length ≤ as.length at hq
  change rs.length ≤ bs.length at hr
  change as.length ≤ L at haL
  change bs.length ≤ L at hbL
  have ht : t ≤ 3*L+1 := by dsimp [t]; rw [List.length_append, Complexity.BitEncoding.frame_length]; omega
  have hm : (8*t+7)*t ≤ (8*(3*L+1)+7)*(3*L+1) := Nat.mul_le_mul (by omega) ht
  dsimp [gcdStepTime]
  omega

/-- Two-step halving bounds the real Euclidean execution by binary length,
never by the numeric value of an operand. -/
def gcd_loop (k : ℕ) (v : AddState) (a b L : ℕ)
    (haL : (Computability.encodeNat a).length ≤ L)
    (hbL : (Computability.encodeNat b).length ≤ L) (hk : b < 2^k) :
    EvalsToInTime gcdMachine.step
      (gcdCfg (some (.inl .check)) v (gcdData (Computability.encodeNat a) (Computability.encodeNat b)) emptyDivData)
      (some (gcdCfg none (false, none, none) (gcdData [] []) (divFinal (Computability.encodeNat (Nat.gcd a b)))))
      (2*k*gcdStepTime L + 2*L + 3) := by
  induction k generalizing v a b with
  | zero =>
    have hb : b = 0 := by simp at hk; omega
    subst b
    have h := gcd_stop v (Computability.encodeNat a)
    have hz : Computability.encodeNat 0 = [] := (encodeNat_eq_nil 0).2 rfl
    apply weakenTime (by simpa only [Nat.gcd_zero_right, hz] using h)
    simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
    omega
  | succ k ih =>
    by_cases hb0 : b = 0
    · subst b
      have h := gcd_stop v (Computability.encodeNat a)
      have hz : Computability.encodeNat 0 = [] := (encodeNat_eq_nil 0).2 rfl
      apply weakenTime (by simpa only [Nat.gcd_zero_right, hz] using h)
      omega
    · have hbpos : 0 < b := by omega
      have hrlt := Nat.mod_lt a hbpos
      have hrL : (Computability.encodeNat (a%b)).length ≤ L :=
        (encodeNat_length_mono (Nat.le_of_lt hrlt)).trans hbL
      have h1 := gcd_euclid_run v a b L hbpos haL hbL
      by_cases hr0 : a%b = 0
      · have h2 := gcd_stop (false, none, none) (Computability.encodeNat b)
        have hz : Computability.encodeNat (a%b) = [] := by simp [hr0, Computability.encodeNat, Computability.encodeNum]
        rw [hz] at h1
        have h := EvalsToInTime.trans gcdMachine.step (gcdStepTime L)
          (2*(Computability.encodeNat b).length+3) _ _ _ h1 h2
        have hg : Nat.gcd a b = b := by rw [gcd_euclidean_step, hr0, Nat.gcd_zero_right]
        apply weakenTime (by simpa only [hg] using h)
        have hp : gcdStepTime L ≤ 2*(k+1)*gcdStepTime L :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · have hrpos : 0 < a%b := by omega
        have hr2lt := Nat.mod_lt b hrpos
        have hr2L : (Computability.encodeNat (b%(a%b))).length ≤ L :=
          (encodeNat_length_mono (Nat.le_of_lt hr2lt)).trans hrL
        have hk' := euclidean_two_step_pow a b k hbpos hrpos hk
        have h2 := gcd_euclid_run (false, none, none) b (a%b) L hrpos hbL hrL
        have h3 := ih (false, none, none) (a%b) (b%(a%b)) hrL hr2L hk'
        have h23 := EvalsToInTime.trans gcdMachine.step (gcdStepTime L)
          (2*k*gcdStepTime L+2*L+3) _ _ _ h2 h3
        have h := EvalsToInTime.trans gcdMachine.step (gcdStepTime L)
          ((2*k*gcdStepTime L+2*L+3)+gcdStepTime L) _ _ _ h1 h23
        have ht : ((2*k*gcdStepTime L+2*L+3)+gcdStepTime L)+gcdStepTime L =
            2*(k+1)*gcdStepTime L+2*L+3 := by ring
        rw [ht] at h
        have hg : Nat.gcd a b = Nat.gcd (a%b) (b%(a%b)) := by
          rw [gcd_euclidean_step a b, gcd_euclidean_step b (a%b)]
        simpa [hg] using h


@[simp] theorem gcd_step_parse_bit (v : AddState) (s : GcdData) (d : DivData)
    (b : Bool) (bs ts : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .parseInput)) v {s with b := true :: b :: bs, t := ts} d) =
      some (gcdCfg (some (.inl .parseInput)) (false, some b, none) {s with b := bs, t := b :: ts} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

@[simp] theorem gcd_step_parse_end (v : AddState) (s : GcdData) (d : DivData) (bs ts : List Bool) :
    gcdMachine.step (gcdCfg (some (.inl .parseInput)) v {s with b := false :: bs, t := ts} d) =
      some (gcdCfg (some (.inl .restoreA)) (false, some false, none) {s with b := bs, t := ts} d) := by
  simp [gcdMachine_m_inl, gcdOuterProgram, gcdPop, gcdCfg, GcdData.stacks, step, stepAux]
  funext k; rcases k with k | k <;> cases k <;> simp [GcdData.stacks, DivData.stacks, Function.update, gcd_inl_inj]

def gcd_parse (v : AddState) (s : GcdData) (d : DivData) (as bs ts : List Bool) :
    EvalsToInTime gcdMachine.step
      (gcdCfg (some (.inl .parseInput)) v {s with b := Complexity.BitEncoding.frame as ++ bs, t := ts} d)
      (some (gcdCfg (some (.inl .restoreA)) (false, some false, none)
        {s with b := bs, t := as.reverse ++ ts} d)) (as.length + 1) := by
  induction as generalizing v ts with
  | nil => simpa [Complexity.BitEncoding.frame] using
      oneStep gcdMachine.step (gcd_step_parse_end v s d bs ts)
  | cons b as ih =>
    have h := EvalsToInTime.trans gcdMachine.step 1 (as.length + 1) _ _ _
      (oneStep gcdMachine.step (gcd_step_parse_bit v s d b (Complexity.BitEncoding.frame as ++ bs) ts))
      (ih (false, some b, none) (b :: ts))
    simpa [Complexity.BitEncoding.frame, List.reverse_cons, List.append_assoc] using h

/-- Expansion of the derived bit-time bound. -/
theorem gcd_time_polynomial (n : ℕ) :
    2*n*gcdStepTime n+4*n+5 = 144*n^3+194*n^2+88*n+5 := by
  dsimp [gcdStepTime]
  ring

/-- Complete canonical binary gcd computation with a cubic bit-time bound. -/
def gcd_outputs (a b : ℕ) :
    TM2OutputsInTime gcdMachine
      (Complexity.BitEncoding.frame (Computability.encodeNat a) ++ Computability.encodeNat b)
      (some (Computability.encodeNat (Nat.gcd a b)))
      (let n := (Complexity.BitEncoding.frame (Computability.encodeNat a) ++ Computability.encodeNat b).length
       144*n^3+194*n^2+88*n+5) := by
  let as := Computability.encodeNat a
  let bs := Computability.encodeNat b
  let n := (Complexity.BitEncoding.frame as ++ bs).length
  have hp := gcd_parse (false, none, none) (gcdData [] []) emptyDivData as bs []
  have hr := gcd_restoreA (false, some false, none) (gcdData [] bs) emptyDivData as.reverse []
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at hp hr
  have ha : as.length ≤ n := by dsimp [n]; rw [List.length_append, Complexity.BitEncoding.frame_length]; omega
  have hb : bs.length ≤ n := by dsimp [n]; rw [List.length_append, Complexity.BitEncoding.frame_length]; omega
  have hk : b < 2^bs.length := by simpa [bs] using Nat.lt_size_self b
  have hg := gcd_loop bs.length (false, none, none) a b n ha hb hk
  have hpr := EvalsToInTime.trans gcdMachine.step (as.length+1) (as.length+1) _ _ _ hp hr
  have h := EvalsToInTime.trans gcdMachine.step ((as.length+1)+(as.length+1))
    (2*bs.length*gcdStepTime n+2*n+3) _ _ _ hpr hg
  have hi : initList gcdMachine (Complexity.BitEncoding.frame as ++ bs) =
      gcdCfg (some (.inl .parseInput)) (false, none, none)
        (gcdData [] (Complexity.BitEncoding.frame as ++ bs)) emptyDivData := by
    unfold initList gcdCfg gcdData emptyDivData divData
    congr 1
    funext k; rcases k with k | k <;> cases k <;> rfl
  have ho : haltList gcdMachine (Computability.encodeNat (Nat.gcd a b)) =
      gcdCfg none (false, none, none) (gcdData [] [])
        (divFinal (Computability.encodeNat (Nat.gcd a b))) := by
    unfold haltList gcdCfg gcdData divFinal
    congr 1
    funext k; rcases k with k | k <;> cases k <;> rfl
  change EvalsToInTime gcdMachine.step (initList gcdMachine (Complexity.BitEncoding.frame as ++ bs))
    (some (haltList gcdMachine (Computability.encodeNat (Nat.gcd a b)))) _
  rw [hi, ho]
  apply weakenTime h
  change _ ≤ 144*n^3+194*n^2+88*n+5
  rw [← gcd_time_polynomial]
  have hm : 2*bs.length*gcdStepTime n ≤ 2*n*gcdStepTime n := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Actual polynomial-time Euclidean gcd in the project's framed binary codec. -/
noncomputable def gcdComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat).toFinEncoding
      Complexity.BitEncoding.nat.toFinEncoding (fun p : ℕ × ℕ => Nat.gcd p.1 p.2) where
  tm := gcdMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 144 * Polynomial.X^3 + Polynomial.C 194 * Polynomial.X^2 +
    Polynomial.C 88 * Polynomial.X + Polynomial.C 5
  outputsFun p := by
    simpa [Complexity.BitEncoding.nat, Complexity.BitEncoding.prod,
      Complexity.BitEncoding.toFinEncoding, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Equiv.refl, Equiv.symm] using gcd_outputs p.1 p.2

theorem fp_gcd :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.nat Complexity.BitEncoding.nat)
      Complexity.BitEncoding.nat (fun p : ℕ × ℕ => Nat.gcd p.1 p.2) := ⟨gcdComputable⟩

end PlanarHom.BinaryArithmetic
