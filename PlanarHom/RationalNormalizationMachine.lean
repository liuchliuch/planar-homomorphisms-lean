import PlanarHom.RationalNormalizationBits
import PlanarHom.BinaryGcdMachine
import PlanarHom.ReturningBitSubroutine

/-! # Canonical signed rational normalization by real gcd and division subroutines -/
namespace PlanarHom.BinaryArithmetic
open Turing Turing.TM2
open PlanarHom.ReturningBitSubroutine

inductive NormLocal | num | den | gcd | sign | tmp | tmp2 | mag deriving DecidableEq, Fintype
inductive NormStack
  | work : NormLocal → NormStack
  | gcd : GcdStack ⊕ DivStack → NormStack
  | divide : DivStack → NormStack
  deriving DecidableEq, Fintype
inductive NormPhase
  | readSign
  | parseNum
  | restoreInput
  | checkDen
  | copyNum
  | restoreNumCopy
  | restoreMagnitude
  | checkSign
  | increment
  | restoreIncrement
  | copyDen
  | restoreDenCopy
  | copyGcdInput
  | gcdDelimiter
  | reverseMagnitude
  | frameGcd
  | afterGcd
  | restoreGcd
  | copyGcd
  | restoreGcdCopy
  | copyNumInput
  | numDelimiter
  | reverseNum
  | frameNum
  | afterNum
  | clearNumRemainder
  | restoreNum
  | moveGcd
  | copyDenInput
  | denDelimiter
  | reverseDen
  | frameDen
  | afterDen
  | clearDenRemainder
  | restoreDen
  | reverseOutputDen
  | outputDen
  | outputDelimiter
  | reverseOutputNum
  | frameOutputNum
  | outputTag
  | clearZeroNum
  | outputZero
  deriving DecidableEq, Fintype
inductive NormLabel
  | work : NormPhase → NormLabel
  | gcd : GcdLabel ⊕ DivLabel → NormLabel
  | numDiv : DivLabel → NormLabel
  | denDiv : DivLabel → NormLabel
  deriving DecidableEq, Fintype

structure NormData where
  num : List Bool
  den : List Bool
  gcd : List Bool
  sign : List Bool
  tmp : List Bool
  tmp2 : List Bool
  mag : List Bool
  go : GcdData
  gi : DivData
  di : DivData

def NormData.stacks (s : NormData) : NormStack → List Bool
  | .work .num => s.num | .work .den => s.den | .work .gcd => s.gcd
  | .work .sign => s.sign | .work .tmp => s.tmp | .work .tmp2 => s.tmp2 | .work .mag => s.mag
  | .gcd (.inl k) => s.go.stacks k
  | .gcd (.inr k) => s.gi.stacks k
  | .divide k => s.di.stacks k

def normData (sign : Bool) (num den : List Bool) : NormData :=
  ⟨num, den, [], [sign], [], [], [], gcdData [] [], emptyDivData, emptyDivData⟩

def normInitial (xs : List Bool) : NormData :=
  ⟨[], xs, [], [], [], [], [], gcdData [] [], emptyDivData, emptyDivData⟩

def normFinal (xs : List Bool) : NormData :=
  ⟨[], [], [], [], [], [], [], gcdData [] [], emptyDivData, divFinal xs⟩

def normGcdEmbedding : (GcdStack ⊕ DivStack) ↪ NormStack := ⟨NormStack.gcd, fun _ _ h => NormStack.gcd.inj h⟩
def normDivEmbedding : DivStack ↪ NormStack := ⟨NormStack.divide, fun _ _ h => NormStack.divide.inj h⟩

abbrev NormStmt := Stmt (fun _ : NormStack => Bool) NormLabel AddState

def normPop (k : NormStack) (q : NormStmt) : NormStmt :=
  .pop k (fun _ b => (false, b, none)) q

def normMove (src dst : NormStack) (again next : NormPhase) : NormStmt :=
  normPop src <| .branch (fun v => v.2.1.isSome)
    (.push dst (fun v => v.2.1.getD false) (.goto (fun _ => .work again)))
    (.goto (fun _ => .work next))

def normClear (src : NormStack) (again next : NormPhase) : NormStmt :=
  normPop src <| .branch (fun v => v.2.1.isSome)
    (.goto (fun _ => .work again)) (.goto (fun _ => .work next))

def normCopy (src : NormStack) (again next : NormPhase) : NormStmt :=
  normPop src <| .branch (fun v => v.2.1.isSome)
    (.push (.work .tmp) (fun v => v.2.1.getD false) <|
      .push (.work .tmp2) (fun v => v.2.1.getD false) (.goto (fun _ => .work again)))
    (.goto (fun _ => .work next))

def normFrame (dst : NormStack) (again : NormPhase) (next : NormLabel) : NormStmt :=
  normPop (.work .tmp) <| .branch (fun v => v.2.1.isSome)
    (.push dst (fun v => v.2.1.getD false) <|
      .push dst (fun _ => true) (.goto (fun _ => .work again)))
    (.goto (fun _ => next))

def normParse (src : NormStack) (again next : NormPhase) : NormStmt :=
  normPop src <| .branch (fun v => v.2.1.getD false)
    (normPop src <| .push (.work .tmp) (fun v => v.2.1.getD false) (.goto (fun _ => .work again)))
    (.goto (fun _ => .work next))

def normLocalProgram : NormPhase → NormStmt
  | .readSign => normPop (.work .den) <| normPop (.work .den) <| normPop (.work .den) <|
      normPop (.work .den) <| .push (.work .sign) (fun v => v.2.1.getD false) <|
        normPop (.work .den) <| normPop (.work .den) (.goto (fun _ => .work .parseNum))
  | .parseNum => normParse (.work .den) .parseNum .restoreInput
  | .restoreInput => normMove (.work .tmp) (.work .num) .restoreInput .checkDen
  | .checkDen => .peek (.work .den) (fun _ b => (false,b,none)) <|
      .branch (fun v => v.2.1.isSome) (.goto (fun _ => .work .copyNum))
        (.goto (fun _ => .work .clearZeroNum))
  | .copyNum => normCopy (.work .num) .copyNum .restoreNumCopy
  | .restoreNumCopy => normMove (.work .tmp) (.work .num) .restoreNumCopy .restoreMagnitude
  | .restoreMagnitude => normMove (.work .tmp2) (.work .mag) .restoreMagnitude .checkSign
  | .checkSign => .peek (.work .sign) (fun _ b => (false,b,none)) <|
      .branch (fun v => v.2.1.getD false) (.load (fun _ => (false,none,none)) (.goto (fun _ => .work .increment)))
        (.load (fun _ => (false,none,none)) (.goto (fun _ => .work .copyDen)))
  | .increment => normPop (.work .mag) <|
      .branch (fun v => v.2.1.getD false)
        (.push (.work .tmp) (fun _ => false) (.goto (fun _ => .work .increment)))
        (.push (.work .mag) (fun _ => true) (.goto (fun _ => .work .restoreIncrement)))
  | .restoreIncrement => normMove (.work .tmp) (.work .mag) .restoreIncrement .copyDen
  | .copyDen => normCopy (.work .den) .copyDen .restoreDenCopy
  | .restoreDenCopy => normMove (.work .tmp) (.work .den) .restoreDenCopy .copyGcdInput
  | .copyGcdInput => normMove (.work .tmp2) (.gcd (.inl .b)) .copyGcdInput .gcdDelimiter
  | .gcdDelimiter => .push (.gcd (.inl .b)) (fun _ => false) (.goto (fun _ => .work .reverseMagnitude))
  | .reverseMagnitude => normMove (.work .mag) (.work .tmp) .reverseMagnitude .frameGcd
  | .frameGcd => normFrame (.gcd (.inl .b)) .frameGcd (.gcd (.inl .parseInput))
  | .afterGcd => normMove (.gcd (.inr .out)) (.work .tmp) .afterGcd .restoreGcd
  | .restoreGcd => normMove (.work .tmp) (.work .gcd) .restoreGcd .copyGcd
  | .copyGcd => normCopy (.work .gcd) .copyGcd .restoreGcdCopy
  | .restoreGcdCopy => normMove (.work .tmp) (.work .gcd) .restoreGcdCopy .copyNumInput
  | .copyNumInput => normMove (.work .tmp2) (.divide .ds) .copyNumInput .numDelimiter
  | .numDelimiter => .push (.divide .ds) (fun _ => false) (.goto (fun _ => .work .reverseNum))
  | .reverseNum => normMove (.work .num) (.work .tmp) .reverseNum .frameNum
  | .frameNum => normFrame (.divide .ds) .frameNum (.numDiv .parse)
  | .afterNum => normParse (.divide .out) .afterNum .clearNumRemainder
  | .clearNumRemainder => normClear (.divide .out) .clearNumRemainder .restoreNum
  | .restoreNum => normMove (.work .tmp) (.work .num) .restoreNum .moveGcd
  | .moveGcd => normMove (.work .gcd) (.work .tmp) .moveGcd .copyDenInput
  | .copyDenInput => normMove (.work .tmp) (.divide .ds) .copyDenInput .denDelimiter
  | .denDelimiter => .push (.divide .ds) (fun _ => false) (.goto (fun _ => .work .reverseDen))
  | .reverseDen => normMove (.work .den) (.work .tmp) .reverseDen .frameDen
  | .frameDen => normFrame (.divide .ds) .frameDen (.denDiv .parse)
  | .afterDen => normParse (.divide .out) .afterDen .clearDenRemainder
  | .clearDenRemainder => normClear (.divide .out) .clearDenRemainder .restoreDen
  | .restoreDen => normMove (.work .tmp) (.work .den) .restoreDen .reverseOutputDen
  | .reverseOutputDen => normMove (.work .den) (.work .tmp) .reverseOutputDen .outputDen
  | .outputDen => normMove (.work .tmp) (.divide .out) .outputDen .outputDelimiter
  | .outputDelimiter => .push (.divide .out) (fun _ => false) (.goto (fun _ => .work .reverseOutputNum))
  | .reverseOutputNum => normMove (.work .num) (.work .tmp) .reverseOutputNum .frameOutputNum
  | .frameOutputNum => normFrame (.divide .out) .frameOutputNum (.work .outputTag)
  | .outputTag => normPop (.work .sign) <|
      .push (.divide .out) (fun _ => false) <| .push (.divide .out) (fun _ => true) <|
      .push (.divide .out) (fun v => v.2.1.getD false) <| .push (.divide .out) (fun _ => true) <|
      .push (.divide .out) (fun _ => true) <| .push (.divide .out) (fun _ => true) <|
      .load (fun _ => (false,none,none)) .halt
  | .clearZeroNum => normClear (.work .num) .clearZeroNum .outputZero
  | .outputZero => normPop (.work .sign) <|
      .push (.divide .out) (fun _ => true) <| .push (.divide .out) (fun _ => false) <|
      .push (.divide .out) (fun _ => false) <| .push (.divide .out) (fun _ => true) <|
      .push (.divide .out) (fun _ => false) <| .push (.divide .out) (fun _ => true) <|
      .push (.divide .out) (fun _ => true) <| .push (.divide .out) (fun _ => true) <|
      .load (fun _ => (false,none,none)) .halt

def rationalNormalizationMachine : FinTM2 where
  K := NormStack
  k₀ := .work .den
  k₁ := .divide .out
  Γ _ := Bool
  Λ := NormLabel
  main := .work .readSign
  σ := AddState
  initialState := (false,none,none)
  m
    | .work l => normLocalProgram l
    | .gcd l => compile normGcdEmbedding NormLabel.gcd (dropUnit AddState) (.work .afterGcd) (gcdMachine.m l)
    | .numDiv l => compile normDivEmbedding NormLabel.numDiv (Equiv.refl AddState) (.work .afterNum) (divisionMachine.m l)
    | .denDiv l => compile normDivEmbedding NormLabel.denDiv (Equiv.refl AddState) (.work .afterDen) (divisionMachine.m l)

@[simp] theorem normMachine_m_local (l : NormPhase) :
    rationalNormalizationMachine.m (.work l) = normLocalProgram l := rfl

@[simp] theorem norm_local_inj (j k : NormLocal) :
    @Eq rationalNormalizationMachine.K (NormStack.work j) (NormStack.work k) ↔ j = k :=
  ⟨NormStack.work.inj, congrArg NormStack.work⟩
@[simp] theorem norm_gcd_inj (j k : GcdStack ⊕ DivStack) :
    @Eq rationalNormalizationMachine.K (NormStack.gcd j) (NormStack.gcd k) ↔ j = k :=
  ⟨NormStack.gcd.inj, congrArg NormStack.gcd⟩
@[simp] theorem norm_divide_inj (j k : DivStack) :
    @Eq rationalNormalizationMachine.K (NormStack.divide j) (NormStack.divide k) ↔ j = k :=
  ⟨NormStack.divide.inj, congrArg NormStack.divide⟩

def normCfg (l : Option NormLabel) (v : AddState) (s : NormData) : rationalNormalizationMachine.Cfg :=
  ⟨l,v,s.stacks⟩

@[simp] theorem norm_step_restoreInput_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreInput)) v {s with tmp := b :: as, num := bs}) =
      some (normCfg (some (.work .restoreInput)) (false,some b,none) {s with tmp := as, num := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreInput_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreInput)) v {s with tmp := [], num := bs}) =
      some (normCfg (some (.work .checkDen)) (false,none,none) {s with tmp := [], num := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreInput (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreInput)) v {s with tmp := as, num := bs})
      (some (normCfg (some (.work .checkDen)) (false,none,none) {s with tmp := [], num := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreInput_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreInput_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_restoreNumCopy_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreNumCopy)) v {s with tmp := b :: as, num := bs}) =
      some (normCfg (some (.work .restoreNumCopy)) (false,some b,none) {s with tmp := as, num := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreNumCopy_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreNumCopy)) v {s with tmp := [], num := bs}) =
      some (normCfg (some (.work .restoreMagnitude)) (false,none,none) {s with tmp := [], num := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreNumCopy (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreNumCopy)) v {s with tmp := as, num := bs})
      (some (normCfg (some (.work .restoreMagnitude)) (false,none,none) {s with tmp := [], num := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreNumCopy_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreNumCopy_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_restoreMagnitude_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreMagnitude)) v {s with tmp2 := b :: as, mag := bs}) =
      some (normCfg (some (.work .restoreMagnitude)) (false,some b,none) {s with tmp2 := as, mag := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreMagnitude_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreMagnitude)) v {s with tmp2 := [], mag := bs}) =
      some (normCfg (some (.work .checkSign)) (false,none,none) {s with tmp2 := [], mag := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreMagnitude (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreMagnitude)) v {s with tmp2 := as, mag := bs})
      (some (normCfg (some (.work .checkSign)) (false,none,none) {s with tmp2 := [], mag := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreMagnitude_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreMagnitude_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_restoreIncrement_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreIncrement)) v {s with tmp := b :: as, mag := bs}) =
      some (normCfg (some (.work .restoreIncrement)) (false,some b,none) {s with tmp := as, mag := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreIncrement_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreIncrement)) v {s with tmp := [], mag := bs}) =
      some (normCfg (some (.work .copyDen)) (false,none,none) {s with tmp := [], mag := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreIncrement (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreIncrement)) v {s with tmp := as, mag := bs})
      (some (normCfg (some (.work .copyDen)) (false,none,none) {s with tmp := [], mag := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreIncrement_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreIncrement_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_restoreDenCopy_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreDenCopy)) v {s with tmp := b :: as, den := bs}) =
      some (normCfg (some (.work .restoreDenCopy)) (false,some b,none) {s with tmp := as, den := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreDenCopy_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreDenCopy)) v {s with tmp := [], den := bs}) =
      some (normCfg (some (.work .copyGcdInput)) (false,none,none) {s with tmp := [], den := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreDenCopy (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreDenCopy)) v {s with tmp := as, den := bs})
      (some (normCfg (some (.work .copyGcdInput)) (false,none,none) {s with tmp := [], den := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreDenCopy_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreDenCopy_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_copyGcdInput_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyGcdInput)) v {s with tmp2 := b :: as, go := {s.go with b := bs}}) =
      some (normCfg (some (.work .copyGcdInput)) (false,some b,none) {s with tmp2 := as, go := {s.go with b := b :: bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, GcdData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update, norm_gcd_inj, Sum.inl.injEq]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_copyGcdInput_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyGcdInput)) v {s with tmp2 := [], go := {s.go with b := bs}}) =
      some (normCfg (some (.work .gcdDelimiter)) (false,none,none) {s with tmp2 := [], go := {s.go with b := bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, GcdData.stacks, step, stepAux]

def norm_copyGcdInput (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .copyGcdInput)) v {s with tmp2 := as, go := {s.go with b := bs}})
      (some (normCfg (some (.work .gcdDelimiter)) (false,none,none) {s with tmp2 := [], go := {s.go with b := as.reverse ++ bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_copyGcdInput_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_copyGcdInput_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_reverseMagnitude_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseMagnitude)) v {s with mag := b :: as, tmp := bs}) =
      some (normCfg (some (.work .reverseMagnitude)) (false,some b,none) {s with mag := as, tmp := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_reverseMagnitude_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseMagnitude)) v {s with mag := [], tmp := bs}) =
      some (normCfg (some (.work .frameGcd)) (false,none,none) {s with mag := [], tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_reverseMagnitude (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .reverseMagnitude)) v {s with mag := as, tmp := bs})
      (some (normCfg (some (.work .frameGcd)) (false,none,none) {s with mag := [], tmp := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_reverseMagnitude_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_reverseMagnitude_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_afterGcd_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .afterGcd)) v {s with gi := {s.gi with out := b :: as}, tmp := bs}) =
      some (normCfg (some (.work .afterGcd)) (false,some b,none) {s with gi := {s.gi with out := as}, tmp := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update, norm_gcd_inj, Sum.inr.injEq]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_afterGcd_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .afterGcd)) v {s with gi := {s.gi with out := []}, tmp := bs}) =
      some (normCfg (some (.work .restoreGcd)) (false,none,none) {s with gi := {s.gi with out := []}, tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]

def norm_afterGcd (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .afterGcd)) v {s with gi := {s.gi with out := as}, tmp := bs})
      (some (normCfg (some (.work .restoreGcd)) (false,none,none) {s with gi := {s.gi with out := []}, tmp := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_afterGcd_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_afterGcd_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_restoreGcd_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreGcd)) v {s with tmp := b :: as, gcd := bs}) =
      some (normCfg (some (.work .restoreGcd)) (false,some b,none) {s with tmp := as, gcd := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreGcd_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreGcd)) v {s with tmp := [], gcd := bs}) =
      some (normCfg (some (.work .copyGcd)) (false,none,none) {s with tmp := [], gcd := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreGcd (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreGcd)) v {s with tmp := as, gcd := bs})
      (some (normCfg (some (.work .copyGcd)) (false,none,none) {s with tmp := [], gcd := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreGcd_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreGcd_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_restoreGcdCopy_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreGcdCopy)) v {s with tmp := b :: as, gcd := bs}) =
      some (normCfg (some (.work .restoreGcdCopy)) (false,some b,none) {s with tmp := as, gcd := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreGcdCopy_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreGcdCopy)) v {s with tmp := [], gcd := bs}) =
      some (normCfg (some (.work .copyNumInput)) (false,none,none) {s with tmp := [], gcd := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreGcdCopy (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreGcdCopy)) v {s with tmp := as, gcd := bs})
      (some (normCfg (some (.work .copyNumInput)) (false,none,none) {s with tmp := [], gcd := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreGcdCopy_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreGcdCopy_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_copyNumInput_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyNumInput)) v {s with tmp2 := b :: as, di := {s.di with ds := bs}}) =
      some (normCfg (some (.work .copyNumInput)) (false,some b,none) {s with tmp2 := as, di := {s.di with ds := b :: bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]

@[simp] theorem norm_step_copyNumInput_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyNumInput)) v {s with tmp2 := [], di := {s.di with ds := bs}}) =
      some (normCfg (some (.work .numDelimiter)) (false,none,none) {s with tmp2 := [], di := {s.di with ds := bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]

def norm_copyNumInput (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .copyNumInput)) v {s with tmp2 := as, di := {s.di with ds := bs}})
      (some (normCfg (some (.work .numDelimiter)) (false,none,none) {s with tmp2 := [], di := {s.di with ds := as.reverse ++ bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_copyNumInput_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_copyNumInput_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_reverseNum_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseNum)) v {s with num := b :: as, tmp := bs}) =
      some (normCfg (some (.work .reverseNum)) (false,some b,none) {s with num := as, tmp := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_reverseNum_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseNum)) v {s with num := [], tmp := bs}) =
      some (normCfg (some (.work .frameNum)) (false,none,none) {s with num := [], tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_reverseNum (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .reverseNum)) v {s with num := as, tmp := bs})
      (some (normCfg (some (.work .frameNum)) (false,none,none) {s with num := [], tmp := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_reverseNum_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_reverseNum_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_restoreNum_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreNum)) v {s with tmp := b :: as, num := bs}) =
      some (normCfg (some (.work .restoreNum)) (false,some b,none) {s with tmp := as, num := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreNum_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreNum)) v {s with tmp := [], num := bs}) =
      some (normCfg (some (.work .moveGcd)) (false,none,none) {s with tmp := [], num := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreNum (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreNum)) v {s with tmp := as, num := bs})
      (some (normCfg (some (.work .moveGcd)) (false,none,none) {s with tmp := [], num := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreNum_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreNum_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_moveGcd_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .moveGcd)) v {s with gcd := b :: as, tmp := bs}) =
      some (normCfg (some (.work .moveGcd)) (false,some b,none) {s with gcd := as, tmp := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_moveGcd_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .moveGcd)) v {s with gcd := [], tmp := bs}) =
      some (normCfg (some (.work .copyDenInput)) (false,none,none) {s with gcd := [], tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_moveGcd (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .moveGcd)) v {s with gcd := as, tmp := bs})
      (some (normCfg (some (.work .copyDenInput)) (false,none,none) {s with gcd := [], tmp := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_moveGcd_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_moveGcd_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_copyDenInput_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyDenInput)) v {s with tmp := b :: as, di := {s.di with ds := bs}}) =
      some (normCfg (some (.work .copyDenInput)) (false,some b,none) {s with tmp := as, di := {s.di with ds := b :: bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]

@[simp] theorem norm_step_copyDenInput_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyDenInput)) v {s with tmp := [], di := {s.di with ds := bs}}) =
      some (normCfg (some (.work .denDelimiter)) (false,none,none) {s with tmp := [], di := {s.di with ds := bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]

def norm_copyDenInput (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .copyDenInput)) v {s with tmp := as, di := {s.di with ds := bs}})
      (some (normCfg (some (.work .denDelimiter)) (false,none,none) {s with tmp := [], di := {s.di with ds := as.reverse ++ bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_copyDenInput_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_copyDenInput_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_reverseDen_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseDen)) v {s with den := b :: as, tmp := bs}) =
      some (normCfg (some (.work .reverseDen)) (false,some b,none) {s with den := as, tmp := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_reverseDen_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseDen)) v {s with den := [], tmp := bs}) =
      some (normCfg (some (.work .frameDen)) (false,none,none) {s with den := [], tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_reverseDen (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .reverseDen)) v {s with den := as, tmp := bs})
      (some (normCfg (some (.work .frameDen)) (false,none,none) {s with den := [], tmp := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_reverseDen_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_reverseDen_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_restoreDen_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreDen)) v {s with tmp := b :: as, den := bs}) =
      some (normCfg (some (.work .restoreDen)) (false,some b,none) {s with tmp := as, den := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_restoreDen_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .restoreDen)) v {s with tmp := [], den := bs}) =
      some (normCfg (some (.work .reverseOutputDen)) (false,none,none) {s with tmp := [], den := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_restoreDen (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .restoreDen)) v {s with tmp := as, den := bs})
      (some (normCfg (some (.work .reverseOutputDen)) (false,none,none) {s with tmp := [], den := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_restoreDen_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_restoreDen_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_reverseOutputDen_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseOutputDen)) v {s with den := b :: as, tmp := bs}) =
      some (normCfg (some (.work .reverseOutputDen)) (false,some b,none) {s with den := as, tmp := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_reverseOutputDen_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseOutputDen)) v {s with den := [], tmp := bs}) =
      some (normCfg (some (.work .outputDen)) (false,none,none) {s with den := [], tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_reverseOutputDen (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .reverseOutputDen)) v {s with den := as, tmp := bs})
      (some (normCfg (some (.work .outputDen)) (false,none,none) {s with den := [], tmp := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_reverseOutputDen_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_reverseOutputDen_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_outputDen_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .outputDen)) v {s with tmp := b :: as, di := {s.di with out := bs}}) =
      some (normCfg (some (.work .outputDen)) (false,some b,none) {s with tmp := as, di := {s.di with out := b :: bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]

@[simp] theorem norm_step_outputDen_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .outputDen)) v {s with tmp := [], di := {s.di with out := bs}}) =
      some (normCfg (some (.work .outputDelimiter)) (false,none,none) {s with tmp := [], di := {s.di with out := bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]

def norm_outputDen (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .outputDen)) v {s with tmp := as, di := {s.di with out := bs}})
      (some (normCfg (some (.work .outputDelimiter)) (false,none,none) {s with tmp := [], di := {s.di with out := as.reverse ++ bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_outputDen_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_outputDen_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_reverseOutputNum_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseOutputNum)) v {s with num := b :: as, tmp := bs}) =
      some (normCfg (some (.work .reverseOutputNum)) (false,some b,none) {s with num := as, tmp := b :: bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_reverseOutputNum_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .reverseOutputNum)) v {s with num := [], tmp := bs}) =
      some (normCfg (some (.work .frameOutputNum)) (false,none,none) {s with num := [], tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normMove, normPop, normCfg, NormData.stacks, step, stepAux]

def norm_reverseOutputNum (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .reverseOutputNum)) v {s with num := as, tmp := bs})
      (some (normCfg (some (.work .frameOutputNum)) (false,none,none) {s with num := [], tmp := as.reverse ++ bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_reverseOutputNum_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_reverseOutputNum_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons, List.append_assoc] using h


/-- Exact-time call to the already verified gcd machine, preserving every
normalizer-owned word and the independent division bank. -/
def norm_call_gcd (s : NormData) (a b : ℕ) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.gcd (.inl .parseInput))) (false,none,none)
        {s with go := gcdData [] (Complexity.BitEncoding.frame (Computability.encodeNat a) ++
          Computability.encodeNat b), gi := emptyDivData})
      (some (normCfg (some (.work .afterGcd)) (false,none,none)
        {s with go := gcdData [] [], gi := divFinal (Computability.encodeNat (Nat.gcd a b))}))
      (let n := (Complexity.BitEncoding.frame (Computability.encodeNat a) ++ Computability.encodeNat b).length
       144*n^3+194*n^2+88*n+5) := by
  apply PlanarHom.ReturningBitSubroutine.run normGcdEmbedding NormLabel.gcd (dropUnit AddState)
    (.work .afterGcd) s.stacks gcdMachine.m rationalNormalizationMachine.m
    (fun _ => rfl) _ _ _ _ _ (gcd_outputs a b)
  · refine ⟨rfl,rfl,?_,?_⟩
    · intro k; rcases k with k | k <;> cases k <;> rfl
    · intro j hj
      cases j with
      | work k => cases k <;> rfl
      | gcd k => exact False.elim (hj k rfl)
      | divide k => rfl
  · refine ⟨rfl,rfl,?_,?_⟩
    · intro k; rcases k with k | k <;> cases k <;> rfl
    · intro j hj
      cases j with
      | work k => cases k <;> rfl
      | gcd k => exact False.elim (hj k rfl)
      | divide k => rfl

def normDivLabels (denominator : Bool) : DivLabel → NormLabel :=
  if denominator then NormLabel.denDiv else NormLabel.numDiv

def normDivReturn (denominator : Bool) : NormLabel :=
  .work (if denominator then .afterDen else .afterNum)

/-- Both natural quotients use the same real division bank, with distinct finite
return labels. The unrelated words and gcd bank are preserved. -/
def norm_call_division (denominator : Bool) (s : NormData) (a b : ℕ) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (normDivLabels denominator .parse)) (false,none,none)
        {s with di := divData (Complexity.BitEncoding.frame (Computability.encodeNat a) ++
          Computability.encodeNat b) [] [] []})
      (some (normCfg (some (normDivReturn denominator)) (false,none,none)
        {s with di := divFinal (Complexity.BitEncoding.frame (Computability.encodeNat (a/b)) ++
          Computability.encodeNat (a%b))}))
      (let n := (Complexity.BitEncoding.frame (Computability.encodeNat a) ++ Computability.encodeNat b).length
       (8*n+7)*n+6*n+9) := by
  have hs := division_outputs (Computability.encodeNat a) (Computability.encodeNat b)
  rw [divBits_encodeNat] at hs
  apply PlanarHom.ReturningBitSubroutine.run normDivEmbedding (normDivLabels denominator)
    (Equiv.refl AddState) (normDivReturn denominator) s.stacks divisionMachine.m rationalNormalizationMachine.m
    (by intro l; cases denominator <;> rfl) _ _ _ _ _ hs
  · refine ⟨?_,rfl,?_,?_⟩
    · cases denominator <;> rfl
    · intro k; cases k <;> rfl
    · intro j hj
      cases j with
      | work k => cases k <;> rfl
      | gcd k => cases k <;> rfl
      | divide k => exact False.elim (hj k rfl)
  · refine ⟨rfl,rfl,?_,?_⟩
    · intro k; cases k <;> rfl
    · intro j hj
      cases j with
      | work k => cases k <;> rfl
      | gcd k => cases k <;> rfl
      | divide k => exact False.elim (hj k rfl)

@[simp] theorem norm_step_copyNum_cons (v : AddState) (s : NormData) (b : Bool) (as bs cs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyNum)) v {s with num := b::as, tmp := bs, tmp2 := cs}) =
      some (normCfg (some (.work .copyNum)) (false,some b,none) {s with num := as, tmp := b::bs, tmp2 := b::cs}) := by
  simp [normMachine_m_local, normLocalProgram, normCopy, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]
@[simp] theorem norm_step_copyNum_nil (v : AddState) (s : NormData) (bs cs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyNum)) v {s with num := [], tmp := bs, tmp2 := cs}) =
      some (normCfg (some (.work .restoreNumCopy)) (false,none,none) {s with num := [], tmp := bs, tmp2 := cs}) := by
  simp [normMachine_m_local, normLocalProgram, normCopy, normPop, normCfg, NormData.stacks, step, stepAux]
def norm_copyNum (v : AddState) (s : NormData) (as bs cs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .copyNum)) v {s with num := as, tmp := bs, tmp2 := cs})
      (some (normCfg (some (.work .restoreNumCopy)) (false,none,none) {s with num := [], tmp := as.reverse++bs, tmp2 := as.reverse++cs})) (as.length+1) := by
  induction as generalizing v bs cs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_copyNum_nil v s bs cs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_copyNum_cons v s b as bs cs))
      (ih (false,some b,none) (b::bs) (b::cs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_copyDen_cons (v : AddState) (s : NormData) (b : Bool) (as bs cs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyDen)) v {s with den := b::as, tmp := bs, tmp2 := cs}) =
      some (normCfg (some (.work .copyDen)) (false,some b,none) {s with den := as, tmp := b::bs, tmp2 := b::cs}) := by
  simp [normMachine_m_local, normLocalProgram, normCopy, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]
@[simp] theorem norm_step_copyDen_nil (v : AddState) (s : NormData) (bs cs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyDen)) v {s with den := [], tmp := bs, tmp2 := cs}) =
      some (normCfg (some (.work .restoreDenCopy)) (false,none,none) {s with den := [], tmp := bs, tmp2 := cs}) := by
  simp [normMachine_m_local, normLocalProgram, normCopy, normPop, normCfg, NormData.stacks, step, stepAux]
def norm_copyDen (v : AddState) (s : NormData) (as bs cs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .copyDen)) v {s with den := as, tmp := bs, tmp2 := cs})
      (some (normCfg (some (.work .restoreDenCopy)) (false,none,none) {s with den := [], tmp := as.reverse++bs, tmp2 := as.reverse++cs})) (as.length+1) := by
  induction as generalizing v bs cs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_copyDen_nil v s bs cs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_copyDen_cons v s b as bs cs))
      (ih (false,some b,none) (b::bs) (b::cs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_copyGcd_cons (v : AddState) (s : NormData) (b : Bool) (as bs cs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyGcd)) v {s with gcd := b::as, tmp := bs, tmp2 := cs}) =
      some (normCfg (some (.work .copyGcd)) (false,some b,none) {s with gcd := as, tmp := b::bs, tmp2 := b::cs}) := by
  simp [normMachine_m_local, normLocalProgram, normCopy, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]
@[simp] theorem norm_step_copyGcd_nil (v : AddState) (s : NormData) (bs cs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .copyGcd)) v {s with gcd := [], tmp := bs, tmp2 := cs}) =
      some (normCfg (some (.work .restoreGcdCopy)) (false,none,none) {s with gcd := [], tmp := bs, tmp2 := cs}) := by
  simp [normMachine_m_local, normLocalProgram, normCopy, normPop, normCfg, NormData.stacks, step, stepAux]
def norm_copyGcd (v : AddState) (s : NormData) (as bs cs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .copyGcd)) v {s with gcd := as, tmp := bs, tmp2 := cs})
      (some (normCfg (some (.work .restoreGcdCopy)) (false,none,none) {s with gcd := [], tmp := as.reverse++bs, tmp2 := as.reverse++cs})) (as.length+1) := by
  induction as generalizing v bs cs with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_copyGcd_nil v s bs cs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_copyGcd_cons v s b as bs cs))
      (ih (false,some b,none) (b::bs) (b::cs))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_frameGcd_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .frameGcd)) v {s with tmp := b::as, go := {s.go with b := bs}}) =
      some (normCfg (some (.work .frameGcd)) (false,some b,none) {s with tmp := as, go := {s.go with b := true::b::bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normFrame, normPop, normCfg, NormData.stacks, GcdData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update, norm_gcd_inj, Sum.inl.injEq]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]
@[simp] theorem norm_step_frameGcd_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .frameGcd)) v {s with tmp := [], go := {s.go with b := bs}}) =
      some (normCfg (some (.gcd (.inl .parseInput))) (false,none,none) {s with tmp := [], go := {s.go with b := bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normFrame, normPop, normCfg, NormData.stacks, GcdData.stacks, step, stepAux]
def norm_frameGcd (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .frameGcd)) v {s with tmp := as, go := {s.go with b := bs}})
      (some (normCfg (some (.gcd (.inl .parseInput))) (false,none,none) {s with tmp := [], go := {s.go with b := framePrefix as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep rationalNormalizationMachine.step (norm_step_frameGcd_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_frameGcd_cons v s b as bs))
      (ih (false,some b,none) (true::b::bs))
    simpa [List.reverse_cons, framePrefix, List.append_assoc] using h

@[simp] theorem norm_step_frameNum_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .frameNum)) v {s with tmp := b::as, di := {s.di with ds := bs}}) =
      some (normCfg (some (.work .frameNum)) (false,some b,none) {s with tmp := as, di := {s.di with ds := true::b::bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normFrame, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
@[simp] theorem norm_step_frameNum_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .frameNum)) v {s with tmp := [], di := {s.di with ds := bs}}) =
      some (normCfg (some (.numDiv .parse)) (false,none,none) {s with tmp := [], di := {s.di with ds := bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normFrame, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
def norm_frameNum (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .frameNum)) v {s with tmp := as, di := {s.di with ds := bs}})
      (some (normCfg (some (.numDiv .parse)) (false,none,none) {s with tmp := [], di := {s.di with ds := framePrefix as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep rationalNormalizationMachine.step (norm_step_frameNum_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_frameNum_cons v s b as bs))
      (ih (false,some b,none) (true::b::bs))
    simpa [List.reverse_cons, framePrefix, List.append_assoc] using h

@[simp] theorem norm_step_frameDen_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .frameDen)) v {s with tmp := b::as, di := {s.di with ds := bs}}) =
      some (normCfg (some (.work .frameDen)) (false,some b,none) {s with tmp := as, di := {s.di with ds := true::b::bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normFrame, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
@[simp] theorem norm_step_frameDen_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .frameDen)) v {s with tmp := [], di := {s.di with ds := bs}}) =
      some (normCfg (some (.denDiv .parse)) (false,none,none) {s with tmp := [], di := {s.di with ds := bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normFrame, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
def norm_frameDen (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .frameDen)) v {s with tmp := as, di := {s.di with ds := bs}})
      (some (normCfg (some (.denDiv .parse)) (false,none,none) {s with tmp := [], di := {s.di with ds := framePrefix as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep rationalNormalizationMachine.step (norm_step_frameDen_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_frameDen_cons v s b as bs))
      (ih (false,some b,none) (true::b::bs))
    simpa [List.reverse_cons, framePrefix, List.append_assoc] using h

@[simp] theorem norm_step_frameOutputNum_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .frameOutputNum)) v {s with tmp := b::as, di := {s.di with out := bs}}) =
      some (normCfg (some (.work .frameOutputNum)) (false,some b,none) {s with tmp := as, di := {s.di with out := true::b::bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normFrame, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
@[simp] theorem norm_step_frameOutputNum_nil (v : AddState) (s : NormData) (bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .frameOutputNum)) v {s with tmp := [], di := {s.di with out := bs}}) =
      some (normCfg (some (.work .outputTag)) (false,none,none) {s with tmp := [], di := {s.di with out := bs}}) := by
  simp [normMachine_m_local, normLocalProgram, normFrame, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
def norm_frameOutputNum (v : AddState) (s : NormData) (as bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .frameOutputNum)) v {s with tmp := as, di := {s.di with out := bs}})
      (some (normCfg (some (.work .outputTag)) (false,none,none) {s with tmp := [], di := {s.di with out := framePrefix as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep rationalNormalizationMachine.step (norm_step_frameOutputNum_nil v s bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_frameOutputNum_cons v s b as bs))
      (ih (false,some b,none) (true::b::bs))
    simpa [List.reverse_cons, framePrefix, List.append_assoc] using h

@[simp] theorem norm_step_parseNum_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .parseNum)) v {s with den := true::b::as, tmp := bs}) =
      some (normCfg (some (.work .parseNum)) (false,some b,none) {s with den := as, tmp := b::bs}) := by
  simp [normMachine_m_local, normLocalProgram, normParse, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]
@[simp] theorem norm_step_parseNum_end (v : AddState) (s : NormData) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .parseNum)) v {s with den := false::as, tmp := bs}) =
      some (normCfg (some (.work .restoreInput)) (false,some false,none) {s with den := as, tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normParse, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]
def norm_parseNum (v : AddState) (s : NormData) (as tail bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .parseNum)) v {s with den := Complexity.BitEncoding.frame as ++ tail, tmp := bs})
      (some (normCfg (some (.work .restoreInput)) (false,some false,none) {s with den := tail, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [Complexity.BitEncoding.frame] using oneStep rationalNormalizationMachine.step (norm_step_parseNum_end v s tail bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_parseNum_cons v s b (Complexity.BitEncoding.frame as ++ tail) bs))
      (ih (false,some b,none) (b::bs))
    simpa [Complexity.BitEncoding.frame, List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_afterNum_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .afterNum)) v {s with di := {s.di with out := true::b::as}, tmp := bs}) =
      some (normCfg (some (.work .afterNum)) (false,some b,none) {s with di := {s.di with out := as}, tmp := b::bs}) := by
  simp [normMachine_m_local, normLocalProgram, normParse, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
@[simp] theorem norm_step_afterNum_end (v : AddState) (s : NormData) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .afterNum)) v {s with di := {s.di with out := false::as}, tmp := bs}) =
      some (normCfg (some (.work .clearNumRemainder)) (false,some false,none) {s with di := {s.di with out := as}, tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normParse, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
def norm_afterNum (v : AddState) (s : NormData) (as tail bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .afterNum)) v {s with di := {s.di with out := Complexity.BitEncoding.frame as ++ tail}, tmp := bs})
      (some (normCfg (some (.work .clearNumRemainder)) (false,some false,none) {s with di := {s.di with out := tail}, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [Complexity.BitEncoding.frame] using oneStep rationalNormalizationMachine.step (norm_step_afterNum_end v s tail bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_afterNum_cons v s b (Complexity.BitEncoding.frame as ++ tail) bs))
      (ih (false,some b,none) (b::bs))
    simpa [Complexity.BitEncoding.frame, List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_afterDen_cons (v : AddState) (s : NormData) (b : Bool) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .afterDen)) v {s with di := {s.di with out := true::b::as}, tmp := bs}) =
      some (normCfg (some (.work .afterDen)) (false,some b,none) {s with di := {s.di with out := as}, tmp := b::bs}) := by
  simp [normMachine_m_local, normLocalProgram, normParse, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
@[simp] theorem norm_step_afterDen_end (v : AddState) (s : NormData) (as bs : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .afterDen)) v {s with di := {s.di with out := false::as}, tmp := bs}) =
      some (normCfg (some (.work .clearDenRemainder)) (false,some false,none) {s with di := {s.di with out := as}, tmp := bs}) := by
  simp [normMachine_m_local, normLocalProgram, normParse, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
def norm_afterDen (v : AddState) (s : NormData) (as tail bs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .afterDen)) v {s with di := {s.di with out := Complexity.BitEncoding.frame as ++ tail}, tmp := bs})
      (some (normCfg (some (.work .clearDenRemainder)) (false,some false,none) {s with di := {s.di with out := tail}, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [Complexity.BitEncoding.frame] using oneStep rationalNormalizationMachine.step (norm_step_afterDen_end v s tail bs)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_afterDen_cons v s b (Complexity.BitEncoding.frame as ++ tail) bs))
      (ih (false,some b,none) (b::bs))
    simpa [Complexity.BitEncoding.frame, List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_clearNumRemainder_cons (v : AddState) (s : NormData) (b : Bool) (as : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .clearNumRemainder)) v {s with di := {s.di with out := b::as}}) =
      some (normCfg (some (.work .clearNumRemainder)) (false,some b,none) {s with di := {s.di with out := as}}) := by
  simp [normMachine_m_local, normLocalProgram, normClear, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
@[simp] theorem norm_step_clearNumRemainder_nil (v : AddState) (s : NormData) :
    rationalNormalizationMachine.step (normCfg (some (.work .clearNumRemainder)) v {s with di := {s.di with out := []}}) =
      some (normCfg (some (.work .restoreNum)) (false,none,none) {s with di := {s.di with out := []}}) := by
  simp [normMachine_m_local, normLocalProgram, normClear, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
def norm_clearNumRemainder (v : AddState) (s : NormData) (as : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .clearNumRemainder)) v {s with di := {s.di with out := as}})
      (some (normCfg (some (.work .restoreNum)) (false,none,none) {s with di := {s.di with out := []}})) (as.length+1) := by
  induction as generalizing v with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_clearNumRemainder_nil v s)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_clearNumRemainder_cons v s b as)) (ih (false,some b,none))
    simpa using h

@[simp] theorem norm_step_clearDenRemainder_cons (v : AddState) (s : NormData) (b : Bool) (as : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .clearDenRemainder)) v {s with di := {s.di with out := b::as}}) =
      some (normCfg (some (.work .clearDenRemainder)) (false,some b,none) {s with di := {s.di with out := as}}) := by
  simp [normMachine_m_local, normLocalProgram, normClear, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]
@[simp] theorem norm_step_clearDenRemainder_nil (v : AddState) (s : NormData) :
    rationalNormalizationMachine.step (normCfg (some (.work .clearDenRemainder)) v {s with di := {s.di with out := []}}) =
      some (normCfg (some (.work .restoreDen)) (false,none,none) {s with di := {s.di with out := []}}) := by
  simp [normMachine_m_local, normLocalProgram, normClear, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
def norm_clearDenRemainder (v : AddState) (s : NormData) (as : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .clearDenRemainder)) v {s with di := {s.di with out := as}})
      (some (normCfg (some (.work .restoreDen)) (false,none,none) {s with di := {s.di with out := []}})) (as.length+1) := by
  induction as generalizing v with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_clearDenRemainder_nil v s)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_clearDenRemainder_cons v s b as)) (ih (false,some b,none))
    simpa using h

@[simp] theorem norm_step_clearZeroNum_cons (v : AddState) (s : NormData) (b : Bool) (as : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .clearZeroNum)) v {s with num := b::as}) =
      some (normCfg (some (.work .clearZeroNum)) (false,some b,none) {s with num := as}) := by
  simp [normMachine_m_local, normLocalProgram, normClear, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]
@[simp] theorem norm_step_clearZeroNum_nil (v : AddState) (s : NormData) :
    rationalNormalizationMachine.step (normCfg (some (.work .clearZeroNum)) v {s with num := []}) =
      some (normCfg (some (.work .outputZero)) (false,none,none) {s with num := []}) := by
  simp [normMachine_m_local, normLocalProgram, normClear, normPop, normCfg, NormData.stacks, step, stepAux]
def norm_clearZeroNum (v : AddState) (s : NormData) (as : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step (normCfg (some (.work .clearZeroNum)) v {s with num := as})
      (some (normCfg (some (.work .outputZero)) (false,none,none) {s with num := []})) (as.length+1) := by
  induction as generalizing v with
  | nil => simpa using oneStep rationalNormalizationMachine.step (norm_step_clearZeroNum_nil v s)
  | cons b as ih =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (as.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_clearZeroNum_cons v s b as)) (ih (false,some b,none))
    simpa using h

@[simp] theorem norm_step_gcdDelimiter (v : AddState) (s : NormData) :
    rationalNormalizationMachine.step (normCfg (some (.work .gcdDelimiter)) v s) =
      some (normCfg (some (.work .reverseMagnitude)) v {s with go := {s.go with b := false :: s.go.b}}) := by
  simp [normMachine_m_local, normLocalProgram, normCfg, NormData.stacks, GcdData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update, norm_gcd_inj, Sum.inl.injEq]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update]

@[simp] theorem norm_step_numDelimiter (v : AddState) (s : NormData) :
    rationalNormalizationMachine.step (normCfg (some (.work .numDelimiter)) v s) =
      some (normCfg (some (.work .reverseNum)) v {s with di := {s.di with ds := false :: s.di.ds}}) := by
  simp [normMachine_m_local, normLocalProgram, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]

@[simp] theorem norm_step_denDelimiter (v : AddState) (s : NormData) :
    rationalNormalizationMachine.step (normCfg (some (.work .denDelimiter)) v s) =
      some (normCfg (some (.work .reverseDen)) v {s with di := {s.di with ds := false :: s.di.ds}}) := by
  simp [normMachine_m_local, normLocalProgram, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]

@[simp] theorem norm_step_outputDelimiter (v : AddState) (s : NormData) :
    rationalNormalizationMachine.step (normCfg (some (.work .outputDelimiter)) v s) =
      some (normCfg (some (.work .reverseOutputNum)) v {s with di := {s.di with out := false :: s.di.out}}) := by
  simp [normMachine_m_local, normLocalProgram, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update]
  | gcd k => rcases k with k | k <;> cases k <;> simp [NormData.stacks, GcdData.stacks, DivData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]


@[simp] theorem norm_step_increment_true (v : AddState) (s : NormData) (xs ys : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .increment)) v {s with mag := true::xs, tmp := ys}) =
      some (normCfg (some (.work .increment)) (false,some true,none) {s with mag := xs, tmp := false::ys}) := by
  simp [normMachine_m_local, normLocalProgram, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => cases k <;> simp [NormData.stacks, Function.update]
  | divide k => simp [NormData.stacks, Function.update]

@[simp] theorem norm_step_increment_false (v : AddState) (s : NormData) (xs ys : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .increment)) v {s with mag := false::xs, tmp := ys}) =
      some (normCfg (some (.work .restoreIncrement)) (false,some false,none) {s with mag := true::xs, tmp := ys}) := by
  simp [normMachine_m_local, normLocalProgram, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => cases k <;> simp [NormData.stacks, Function.update]
  | divide k => simp [NormData.stacks, Function.update]

@[simp] theorem norm_step_increment_nil (v : AddState) (s : NormData) (ys : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .increment)) v {s with mag := [], tmp := ys}) =
      some (normCfg (some (.work .restoreIncrement)) (false,none,none) {s with mag := [true], tmp := ys}) := by
  simp [normMachine_m_local, normLocalProgram, normPop, normCfg, NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => cases k <;> simp [NormData.stacks, Function.update]
  | divide k => simp [NormData.stacks, Function.update]

def norm_increment (v : AddState) (s : NormData) (xs ys : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .increment)) v {s with mag := xs, tmp := ys})
      (some (normCfg (some (.work .copyDen)) (false,none,none)
        {s with mag := ys.reverse ++ succBits xs, tmp := []})) (2*xs.length+ys.length+2) := by
  induction xs generalizing v ys with
  | nil =>
    have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (ys.length+1) _ _ _
      (oneStep rationalNormalizationMachine.step (norm_step_increment_nil v s ys))
      (norm_restoreIncrement (false,none,none) s ys [true])
    simpa [succBits] using h
  | cons b xs ih =>
    cases b with
    | false =>
      have h := EvalsToInTime.trans rationalNormalizationMachine.step 1 (ys.length+1) _ _ _
        (oneStep rationalNormalizationMachine.step (norm_step_increment_false v s xs ys))
        (norm_restoreIncrement (false,some false,none) s ys (true::xs))
      apply weakenTime (by simpa [succBits] using h)
      simp
    | true =>
      have h := EvalsToInTime.trans rationalNormalizationMachine.step 1
        (2*xs.length+(false::ys).length+2) _ _ _
        (oneStep rationalNormalizationMachine.step (norm_step_increment_true v s xs ys))
        (ih (false,some true,none) (false::ys))
      have ht : (2*xs.length+(false::ys).length+2)+1 = 2*(true::xs).length+ys.length+2 := by simp; omega
      rw [ht] at h
      simpa [succBits, List.reverse_cons, List.append_assoc] using h

@[simp] theorem norm_step_checkSign (v : AddState) (s : NormData) (sign : Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .checkSign)) v {s with sign := [sign]}) =
      some (normCfg (some (.work (if sign then .increment else .copyDen))) (false,none,none)
        {s with sign := [sign]}) := by
  cases sign <;> simp [normMachine_m_local, normLocalProgram, normCfg, NormData.stacks, step, stepAux]

@[simp] theorem norm_step_checkDen_nil (v : AddState) (s : NormData) :
    rationalNormalizationMachine.step (normCfg (some (.work .checkDen)) v {s with den := []}) =
      some (normCfg (some (.work .clearZeroNum)) (false,none,none) {s with den := []}) := by
  simp [normMachine_m_local, normLocalProgram, normCfg, NormData.stacks, step, stepAux]

@[simp] theorem norm_step_checkDen_nonempty (v : AddState) (s : NormData) (ds : List Bool) (hd : ds ≠ []) :
    rationalNormalizationMachine.step (normCfg (some (.work .checkDen)) v {s with den := ds}) =
      some (normCfg (some (.work .copyNum)) (false,ds.head?,none) {s with den := ds}) := by
  cases ds with
  | nil => contradiction
  | cons b ds => simp [normMachine_m_local, normLocalProgram, normCfg, NormData.stacks, step, stepAux]

@[simp] theorem norm_step_readSign (v : AddState) (sign : Bool) (as ds : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .readSign)) v (normInitial (ratWord sign as ds))) =
      some (normCfg (some (.work .parseNum)) (false,some false,none)
        (normData sign [] (Complexity.BitEncoding.frame as ++ ds))) := by
  simp [normMachine_m_local, normLocalProgram, normPop, normCfg, normInitial, normData, ratWord,
    NormData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => cases k <;> simp [NormData.stacks, Function.update]
  | divide k => simp [NormData.stacks, Function.update]

@[simp] theorem norm_step_outputTag (v : AddState) (s : NormData) (sign : Bool) (out : List Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .outputTag)) v
      {s with sign := [sign], di := {s.di with out := out}}) =
      some (normCfg none (false,none,none)
        {s with sign := [], di := {s.di with out := [true,true,true,sign,true,false] ++ out}}) := by
  simp [normMachine_m_local, normLocalProgram, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => cases k <;> simp [NormData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]

@[simp] theorem norm_step_outputZero (v : AddState) (s : NormData) (sign : Bool) :
    rationalNormalizationMachine.step (normCfg (some (.work .outputZero)) v
      {s with sign := [sign], di := {s.di with out := []}}) =
      some (normCfg none (false,none,none)
        {s with sign := [], di := {s.di with out := [true,true,true,false,true,false,false,true]}}) := by
  simp [normMachine_m_local, normLocalProgram, normPop, normCfg, NormData.stacks, DivData.stacks, step, stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [NormData.stacks, Function.update, norm_local_inj]
  | gcd k => cases k <;> simp [NormData.stacks, Function.update]
  | divide k => cases k <;> simp [NormData.stacks, DivData.stacks, Function.update, norm_divide_inj]

/-- Sequential combination with the time budget written in execution order. -/
def normSeq {A : Type} {f : A → Option A} {a b : A} {c : Option A} {m n : ℕ}
    (h : EvalsToInTime f a (some b) m) (h' : EvalsToInTime f b c n) :
    EvalsToInTime f a c (m+n) := weakenTime (EvalsToInTime.trans f m n a b c h h') (by omega)


/-- A normalization checkpoint with both subroutine banks and local scratch clear. -/
def normReady (sign : Bool) (num den g mag : List Bool) : NormData :=
  ⟨num,den,g,[sign],[],[],mag,gcdData [] [],emptyDivData,emptyDivData⟩

def norm_copy_magnitude (v : AddState) (sign : Bool) (ns ds : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .copyNum)) v (normReady sign ns ds [] []))
      (some (normCfg (some (.work .checkSign)) (false,none,none) (normReady sign ns ds [] ns)))
      (3*ns.length+3) := by
  let s := normReady sign ns ds [] []
  have h1 := norm_copyNum v s ns [] []
  have h2 := norm_restoreNumCopy (false,none,none) {s with num := [], tmp2 := ns.reverse} ns.reverse []
  have h3 := norm_restoreMagnitude (false,none,none) s ns.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2 h3
  have h := normSeq h1 (normSeq h2 h3)
  have ht : (ns.length+1)+((ns.length+1)+(ns.length+1))=3*ns.length+3 := by omega
  rw [ht] at h
  exact h

def norm_choose_magnitude (v : AddState) (sign : Bool) (ns ds : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .checkSign)) v (normReady sign ns ds [] ns))
      (some (normCfg (some (.work .copyDen)) (false,none,none)
        (normReady sign ns ds [] (if sign then succBits ns else ns)))) (2*ns.length+3) := by
  have hc := oneStep rationalNormalizationMachine.step
    (norm_step_checkSign v (normReady sign ns ds [] ns) sign)
  cases sign with
  | false =>
    apply weakenTime (by simpa only [Bool.false_eq_true,↓reduceIte] using hc)
    omega
  | true =>
    have hi := norm_increment (false,none,none) (normReady true ns ds [] ns) ns []
    simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.add_zero] at hi
    have h := normSeq hc hi
    have ht : 1+(2*ns.length+2)=2*ns.length+3 := by omega
    rw [ht] at h
    exact h

def norm_prepare_gcd (v : AddState) (sign : Bool) (ns ds ms : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .copyDen)) v (normReady sign ns ds [] ms))
      (some (normCfg (some (.gcd (.inl .parseInput))) (false,none,none)
        {normReady sign ns ds [] [] with go := gcdData [] (Complexity.BitEncoding.frame ms ++ ds)}))
      (3*ds.length+2*ms.length+6) := by
  let s := normReady sign ns ds [] ms
  have h1 := norm_copyDen v s ds [] []
  have h2 := norm_restoreDenCopy (false,none,none) {s with den := [], tmp2 := ds.reverse} ds.reverse []
  have h3 := norm_copyGcdInput (false,none,none) s ds.reverse []
  have h4 := oneStep rationalNormalizationMachine.step
    (norm_step_gcdDelimiter (false,none,none) {s with go := gcdData [] ds})
  have h5 := norm_reverseMagnitude (false,none,none) {s with go := gcdData [] (false::ds)} ms []
  have h6 := norm_frameGcd (false,none,none) {s with mag := []} ms.reverse (false::ds)
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2 h3 h5 h6
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 (normSeq h5 h6))))
  have ht : (ds.length+1)+((ds.length+1)+((ds.length+1)+(1+((ms.length+1)+(ms.length+1))))) =
      3*ds.length+2*ms.length+6 := by omega
  rw [ht] at h
  simpa only [framePrefix_delimiter] using h

def norm_get_gcd (v : AddState) (sign : Bool) (ns ds gs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .afterGcd)) v {normReady sign ns ds [] [] with gi := divFinal gs})
      (some (normCfg (some (.work .copyGcd)) (false,none,none) (normReady sign ns ds gs [])))
      (2*gs.length+2) := by
  let s := normReady sign ns ds [] []
  have h1 := norm_afterGcd v s gs []
  have h2 := norm_restoreGcd (false,none,none) s gs.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2
  have h := normSeq h1 h2
  have ht : (gs.length+1)+(gs.length+1)=2*gs.length+2 := by omega
  rw [ht] at h
  exact h

def norm_prepare_num (v : AddState) (sign : Bool) (ns ds gs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .copyGcd)) v (normReady sign ns ds gs []))
      (some (normCfg (some (.numDiv .parse)) (false,none,none)
        {normReady sign [] ds gs [] with di := divData (Complexity.BitEncoding.frame ns ++ gs) [] [] []}))
      (3*gs.length+2*ns.length+6) := by
  let s := normReady sign ns ds gs []
  have h1 := norm_copyGcd v s gs [] []
  have h2 := norm_restoreGcdCopy (false,none,none) {s with gcd := [], tmp2 := gs.reverse} gs.reverse []
  have h3 := norm_copyNumInput (false,none,none) s gs.reverse []
  have h4 := oneStep rationalNormalizationMachine.step
    (norm_step_numDelimiter (false,none,none) {s with di := divData gs [] [] []})
  have h5 := norm_reverseNum (false,none,none) {s with di := divData (false::gs) [] [] []} ns []
  have h6 := norm_frameNum (false,none,none) {s with num := []} ns.reverse (false::gs)
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2 h3 h5 h6
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 (normSeq h5 h6))))
  have ht : (gs.length+1)+((gs.length+1)+((gs.length+1)+(1+((ns.length+1)+(ns.length+1))))) =
      3*gs.length+2*ns.length+6 := by omega
  rw [ht] at h
  simpa only [framePrefix_delimiter] using h

def norm_finish_num (v : AddState) (sign : Bool) (ds gs qs rs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .afterNum)) v
        {normReady sign [] ds gs [] with di := divFinal (Complexity.BitEncoding.frame qs ++ rs)})
      (some (normCfg (some (.work .moveGcd)) (false,none,none) (normReady sign qs ds gs [])))
      (2*qs.length+rs.length+3) := by
  let s := normReady sign [] ds gs []
  have h1 := norm_afterNum v s qs rs []
  have h2 := norm_clearNumRemainder (false,some false,none) {s with tmp := qs.reverse} rs
  have h3 := norm_restoreNum (false,none,none) s qs.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h3
  have h := normSeq h1 (normSeq h2 h3)
  have ht : (qs.length+1)+((rs.length+1)+(qs.length+1))=2*qs.length+rs.length+3 := by omega
  rw [ht] at h
  exact h

def norm_prepare_den (v : AddState) (sign : Bool) (ns ds gs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .moveGcd)) v (normReady sign ns ds gs []))
      (some (normCfg (some (.denDiv .parse)) (false,none,none)
        {normReady sign ns [] [] [] with di := divData (Complexity.BitEncoding.frame ds ++ gs) [] [] []}))
      (2*gs.length+2*ds.length+5) := by
  let s := normReady sign ns ds gs []
  have h1 := norm_moveGcd v s gs []
  have h2 := norm_copyDenInput (false,none,none) {s with gcd := []} gs.reverse []
  have h3 := oneStep rationalNormalizationMachine.step
    (norm_step_denDelimiter (false,none,none) {s with gcd := [], di := divData gs [] [] []})
  have h4 := norm_reverseDen (false,none,none) {s with gcd := [], di := divData (false::gs) [] [] []} ds []
  have h5 := norm_frameDen (false,none,none) {s with gcd := [], den := []} ds.reverse (false::gs)
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2 h4 h5
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 h5)))
  have ht : (gs.length+1)+((gs.length+1)+(1+((ds.length+1)+(ds.length+1)))) =
      2*gs.length+2*ds.length+5 := by omega
  rw [ht] at h
  simpa only [framePrefix_delimiter] using h

def norm_finish_den (v : AddState) (sign : Bool) (ns qs rs : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .afterDen)) v
        {normReady sign ns [] [] [] with di := divFinal (Complexity.BitEncoding.frame qs ++ rs)})
      (some (normCfg (some (.work .reverseOutputDen)) (false,none,none) (normReady sign ns qs [] [])))
      (2*qs.length+rs.length+3) := by
  let s := normReady sign ns [] [] []
  have h1 := norm_afterDen v s qs rs []
  have h2 := norm_clearDenRemainder (false,some false,none) {s with tmp := qs.reverse} rs
  have h3 := norm_restoreDen (false,none,none) s qs.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h3
  have h := normSeq h1 (normSeq h2 h3)
  have ht : (qs.length+1)+((rs.length+1)+(qs.length+1))=2*qs.length+rs.length+3 := by omega
  rw [ht] at h
  exact h

def norm_serialize (v : AddState) (sign : Bool) (ns ds : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .reverseOutputDen)) v (normReady sign ns ds [] []))
      (some (normCfg none (false,none,none) (normFinal (ratWord sign ns ds))))
      (2*ds.length+2*ns.length+6) := by
  let s := normReady sign ns ds [] []
  have h1 := norm_reverseOutputDen v s ds []
  have h2 := norm_outputDen (false,none,none) {s with den := []} ds.reverse []
  have h3 := oneStep rationalNormalizationMachine.step
    (norm_step_outputDelimiter (false,none,none) {s with den := [], di := divFinal ds})
  have h4 := norm_reverseOutputNum (false,none,none) {s with den := [], di := divFinal (false::ds)} ns []
  have h5 := norm_frameOutputNum (false,none,none) {s with den := [], num := []} ns.reverse (false::ds)
  have h6 := oneStep rationalNormalizationMachine.step
    (norm_step_outputTag (false,none,none) (normFinal []) sign (Complexity.BitEncoding.frame ns ++ ds))
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil,framePrefix_delimiter] at h1 h2 h4 h5
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 (normSeq h5 h6))))
  have ht : (ds.length+1)+((ds.length+1)+(1+((ns.length+1)+((ns.length+1)+1)))) =
      2*ds.length+2*ns.length+6 := by omega
  rw [ht] at h
  simpa only [ratWord,List.append_assoc] using h

def norm_parse_input (v : AddState) (sign : Bool) (ns ds : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .readSign)) v (normInitial (ratWord sign ns ds)))
      (some (normCfg (some (.work .checkDen)) (false,none,none) (normReady sign ns ds [] [])))
      (2*ns.length+3) := by
  have h1 := oneStep rationalNormalizationMachine.step (norm_step_readSign v sign ns ds)
  have h2 := norm_parseNum (false,some false,none) (normData sign [] ds) ns ds []
  have h3 := norm_restoreInput (false,some false,none) (normData sign [] ds) ns.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h2 h3
  have h := normSeq h1 (normSeq h2 h3)
  have ht : 1+((ns.length+1)+(ns.length+1))=2*ns.length+3 := by omega
  rw [ht] at h
  exact h

def norm_zero (v : AddState) (sign : Bool) (ns : List Bool) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .checkDen)) v (normReady sign ns [] [] []))
      (some (normCfg none (false,none,none) (normFinal [true,true,true,false,true,false,false,true])))
      (ns.length+3) := by
  let s := normReady sign ns [] [] []
  have h1 := oneStep rationalNormalizationMachine.step (norm_step_checkDen_nil v s)
  have h2 := norm_clearZeroNum (false,none,none) s ns
  have h3 := oneStep rationalNormalizationMachine.step (norm_step_outputZero (false,none,none) (normFinal []) sign)
  have h := normSeq h1 (normSeq h2 h3)
  have ht : 1+((ns.length+1)+1)=ns.length+3 := by omega
  rw [ht] at h
  exact h


def normGcdTime (n : ℕ) : ℕ := 144*n^3+194*n^2+88*n+5
def normDivTime (n : ℕ) : ℕ := (8*n+7)*n+6*n+9
def normCoreTime (n : ℕ) : ℕ := normGcdTime (3*n+1)+2*normDivTime (3*n+1)+100*n+100

/-- A nonzero denominator is normalized by one gcd call and two exact natural
quotient calls; all three are actual compiled finite-control programs. -/
def norm_nonzero (v : AddState) (sign : Bool) (n d L : ℕ) (hd : 0 < d)
    (hnL : (Computability.encodeNat n).length+1 ≤ L)
    (hdL : (Computability.encodeNat d).length ≤ L) :
    EvalsToInTime rationalNormalizationMachine.step
      (normCfg (some (.work .checkDen)) v
        (normReady sign (Computability.encodeNat n) (Computability.encodeNat d) [] []))
      (some (normCfg none (false,none,none)
        (normFinal (Complexity.BitEncoding.rat.encode (mkRat (signedIndex sign n) d)))))
      (normCoreTime L) := by
  let m := magnitudeIndex sign n
  let g := Nat.gcd m d
  let ns := Computability.encodeNat n
  let ds := Computability.encodeNat d
  let ms := Computability.encodeNat m
  let gs := Computability.encodeNat g
  let nq := Computability.encodeNat (n/g)
  let nr := Computability.encodeNat (n%g)
  let dq := Computability.encodeNat (d/g)
  let dr := Computability.encodeNat (d%g)
  have hds : ds ≠ [] := by simpa [ds] using hd.ne'
  have hm : (if sign then succBits ns else ns) = ms := by
    cases sign <;> simp [ns,ms,m,magnitudeIndex]
  have h1 := oneStep rationalNormalizationMachine.step
    (norm_step_checkDen_nonempty v (normReady sign ns ds [] []) ds hds)
  have h2 := norm_copy_magnitude (false,ds.head?,none) sign ns ds
  have h3 := norm_choose_magnitude (false,none,none) sign ns ds
  rw [hm] at h3
  have h4 := norm_prepare_gcd (false,none,none) sign ns ds ms
  have h5 := norm_call_gcd (normReady sign ns ds [] []) m d
  have h6 := norm_get_gcd (false,none,none) sign ns ds gs
  have h7 := norm_prepare_num (false,none,none) sign ns ds gs
  have h8 := norm_call_division false (normReady sign [] ds gs []) n g
  have h9 := norm_finish_num (false,none,none) sign ds gs nq nr
  have h10 := norm_prepare_den (false,none,none) sign nq ds gs
  have h11 := norm_call_division true (normReady sign nq [] [] []) d g
  have h12 := norm_finish_den (false,none,none) sign nq dq dr
  have h13 := norm_serialize (false,none,none) sign nq dq
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 (normSeq h5
    (normSeq h6 (normSeq h7 (normSeq h8 (normSeq h9 (normSeq h10 (normSeq h11 (normSeq h12 h13)))))))))))
  rw [encode_mkRat_signedIndex sign n d hd]
  apply weakenTime h
  have hgp : 0 < g := normalization_gcd_pos sign n d hd
  have hgL : gs.length ≤ L := (encodeNat_length_mono (Nat.gcd_le_right m hd)).trans hdL
  have hnq := encodeNat_length_mono (Nat.div_le_self n g)
  have hnr := encodeNat_length_mono (Nat.le_of_lt (Nat.mod_lt n hgp))
  have hdq := encodeNat_length_mono (Nat.div_le_self d g)
  have hdr := encodeNat_length_mono (Nat.le_of_lt (Nat.mod_lt d hgp))
  change nq.length ≤ ns.length at hnq
  change nr.length ≤ gs.length at hnr
  change dq.length ≤ ds.length at hdq
  change dr.length ≤ gs.length at hdr
  change ns.length+1 ≤ L at hnL
  change ds.length ≤ L at hdL
  have hmL : ms.length ≤ L := by
    have hh : (if sign then succBits ns else ns).length ≤ ns.length+1 := by
      cases sign with
      | false => simp
      | true => exact succBits_length_le ns
    rw [hm] at hh
    exact hh.trans hnL
  let cg := (Complexity.BitEncoding.frame ms ++ ds).length
  let cn := (Complexity.BitEncoding.frame ns ++ gs).length
  let cd := (Complexity.BitEncoding.frame ds ++ gs).length
  have hcg : cg ≤ 3*L+1 := by dsimp [cg]; rw [List.length_append,Complexity.BitEncoding.frame_length]; omega
  have hcn : cn ≤ 3*L+1 := by dsimp [cn]; rw [List.length_append,Complexity.BitEncoding.frame_length]; omega
  have hcd : cd ≤ 3*L+1 := by dsimp [cd]; rw [List.length_append,Complexity.BitEncoding.frame_length]; omega
  have hgc : normGcdTime cg ≤ normGcdTime (3*L+1) := by
    have hp2 := Nat.pow_le_pow_left hcg 2
    have hp3 := Nat.pow_le_pow_left hcg 3
    dsimp [normGcdTime]
    omega
  have hnc : normDivTime cn ≤ normDivTime (3*L+1) := by
    have hm := Nat.mul_le_mul (show 8*cn+7 ≤ 8*(3*L+1)+7 by omega) hcn
    dsimp [normDivTime]
    omega
  have hdc : normDivTime cd ≤ normDivTime (3*L+1) := by
    have hm := Nat.mul_le_mul (show 8*cd+7 ≤ 8*(3*L+1)+7 by omega) hcd
    dsimp [normDivTime]
    omega
  change 1+((3*ns.length+3)+((2*ns.length+3)+((3*ds.length+2*ms.length+6)+
    (normGcdTime cg+((2*gs.length+2)+((3*gs.length+2*ns.length+6)+(normDivTime cn+
      ((2*nq.length+nr.length+3)+((2*gs.length+2*ds.length+5)+(normDivTime cd+
        ((2*dq.length+dr.length+3)+(2*dq.length+2*nq.length+6)))))))))))) ≤ normCoreTime L
  dsimp [normCoreTime]
  omega

/-- Expansion of the conservative cubic normalization time bound. -/
theorem norm_time_polynomial (n : ℕ) :
    normCoreTime (n+1)+2*n+3 = 3888*n^3+17442*n^2+26220*n+13258 := by
  dsimp [normCoreTime,normGcdTime,normDivTime]
  ring

/-- Complete canonical `mkRat` computation, including both zero conventions and
the existing signed-index integer codec. -/
def rationalNormalization_outputs (sign : Bool) (n d : ℕ) :
    TM2OutputsInTime rationalNormalizationMachine
      ((Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.nat).encode
        (signedIndex sign n,d))
      (some (Complexity.BitEncoding.rat.encode (mkRat (signedIndex sign n) d)))
      (let N := ((Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.nat).encode
        (signedIndex sign n,d)).length
       3888*N^3+17442*N^2+26220*N+13258) := by
  let ns := Computability.encodeNat n
  let ds := Computability.encodeNat d
  let N := (ratWord sign ns ds).length
  have hn : ns.length+1 ≤ N+1 := by dsimp [N,ratWord]; simp only [List.length_append,Complexity.BitEncoding.frame_length]; omega
  have hd : ds.length ≤ N+1 := by dsimp [N,ratWord]; simp only [List.length_append,Complexity.BitEncoding.frame_length]; omega
  have hp := norm_parse_input (false,none,none) sign ns ds
  have hi : initList rationalNormalizationMachine (ratWord sign ns ds) =
      normCfg (some (.work .readSign)) (false,none,none) (normInitial (ratWord sign ns ds)) := by
    unfold initList normCfg normInitial
    congr 1
    funext k; cases k with
    | work k => cases k <;> rfl
    | gcd k => rcases k with k | k <;> cases k <;> rfl
    | divide k => cases k <;> rfl
  have ho (out : List Bool) : haltList rationalNormalizationMachine out =
      normCfg none (false,none,none) (normFinal out) := by
    unfold haltList normCfg normFinal
    congr 1
    funext k; cases k with
    | work k => cases k <;> rfl
    | gcd k => rcases k with k | k <;> cases k <;> rfl
    | divide k => cases k <;> rfl
  rw [encode_int_nat_pair]
  change EvalsToInTime rationalNormalizationMachine.step
    (initList rationalNormalizationMachine (ratWord sign ns ds))
    (some (haltList rationalNormalizationMachine (Complexity.BitEncoding.rat.encode (mkRat (signedIndex sign n) d))))
    (3888*N^3+17442*N^2+26220*N+13258)
  rw [hi,ho,← norm_time_polynomial]
  by_cases hd0 : d=0
  · subst d
    have hz : ds=[] := (encodeNat_eq_nil 0).2 rfl
    rw [hz] at hp
    have hf := norm_zero (false,none,none) sign ns
    have h := normSeq hp hf
    apply weakenTime (by simpa only [encode_mkRat_zero_den,hz] using h)
    have hn' : ns.length ≤ N := by omega
    dsimp [normCoreTime,normGcdTime,normDivTime]
    omega
  · have hdp : 0<d := by omega
    have hf := norm_nonzero (false,none,none) sign n d (N+1) hdp hn hd
    have h := normSeq hp hf
    apply weakenTime h
    omega

/-- A real polynomial-time normalization machine for the project's canonical
reduced rational encoding. -/
noncomputable def rationalNormalizationComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.nat).toFinEncoding
      Complexity.BitEncoding.rat.toFinEncoding (fun p : ℤ×ℕ => mkRat p.1 p.2) where
  tm := rationalNormalizationMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3888*Polynomial.X^3 + Polynomial.C 17442*Polynomial.X^2 +
    Polynomial.C 26220*Polynomial.X + Polynomial.C 13258
  outputsFun p := by
    rcases p with ⟨z,d⟩
    cases z with
    | ofNat n =>
      simpa [Complexity.BitEncoding.toFinEncoding, signedIndex,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Equiv.refl,Equiv.symm] using
        rationalNormalization_outputs false n d
    | negSucc n =>
      simpa [Complexity.BitEncoding.toFinEncoding, signedIndex,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Equiv.refl,Equiv.symm] using
        rationalNormalization_outputs true n d

theorem fp_rational_normalization :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.nat)
      Complexity.BitEncoding.rat (fun p : ℤ×ℕ => mkRat p.1 p.2) := ⟨rationalNormalizationComputable⟩

end PlanarHom.BinaryArithmetic
