import PlanarHom.RationalMultiplicationBits
import PlanarHom.RationalNormalizationMachine
import PlanarHom.BinaryMultiplicationMachine

/-! # Canonical rational multiplication from explicit bit-machine subroutines -/
namespace PlanarHom.BinaryArithmetic
open Turing Turing.TM2
open PlanarHom.ReturningBitSubroutine

inductive RMLocal | a | b | da | db | sa | sb | tmp deriving DecidableEq,Fintype
inductive RMStack
  | work : RMLocal → RMStack
  | multiply : MulStack → RMStack
  | subtract : Option Bool → RMStack
  | normalize : NormStack → RMStack
  deriving DecidableEq,Fintype
inductive RMPhase
  | unframeFirst
  | restoreFirst
  | readA
  | parseA
  | restoreA
  | readB
  | parseB
  | restoreB
  | checkA
  | incA
  | restoreIncA
  | checkB
  | incB
  | restoreIncB
  | combineSigns
  | moveB
  | inputB
  | numDelimiter
  | reverseA
  | frameNum
  | afterNum
  | restoreProduct
  | checkProduct
  | predInput
  | reversePred
  | framePred
  | afterPred
  | restorePred
  | moveDenB
  | inputDenB
  | denDelimiter
  | reverseDenA
  | frameDen
  | afterDen
  | inputNormDen
  | normDelimiter
  | reverseProduct
  | frameNormalize
  | normTag
  | done
  deriving DecidableEq,Fintype
inductive RMLabel
  | work : RMPhase → RMLabel
  | numMul : MulLabel → RMLabel
  | denMul : MulLabel → RMLabel
  | pred : SubLabel → RMLabel
  | norm : NormLabel → RMLabel
  deriving DecidableEq,Fintype

structure RMulStore where
  input : List Bool
  x : List Bool
  z : List Bool
  sx : List Bool
  sz : List Bool

def RMulStore.stacks (s : RMulStore) : MulStack → List Bool
  | .input => s.input | .x => s.x | .z => s.z | .sx => s.sx | .sz => s.sz

def rmulEmpty : RMulStore := ⟨[],[],[],[],[]⟩

structure RSubStore where
  input : List Bool
  scratch : List Bool
  first : List Bool

def RSubStore.stacks (s : RSubStore) : Option Bool → List Bool
  | none => s.input | some false => s.scratch | some true => s.first

def rsubEmpty : RSubStore := ⟨[],[],[]⟩

structure RMData where
  a : List Bool
  b : List Bool
  da : List Bool
  db : List Bool
  sa : List Bool
  sb : List Bool
  tmp : List Bool
  mp : RMulStore
  sp : RSubStore
  np : NormData

def RMData.stacks (s : RMData) : RMStack → List Bool
  | .work .a => s.a | .work .b => s.b | .work .da => s.da | .work .db => s.db
  | .work .sa => s.sa | .work .sb => s.sb | .work .tmp => s.tmp
  | .multiply k => s.mp.stacks k | .subtract k => s.sp.stacks k | .normalize k => s.np.stacks k

def rmReady (sa sb : Bool) (a b da db : List Bool) : RMData :=
  ⟨a,b,da,db,[sa],[sb],[],rmulEmpty,rsubEmpty,normInitial []⟩
def rmSigned (sign : Bool) (a b da db : List Bool) : RMData :=
  ⟨a,b,da,db,[sign],[],[],rmulEmpty,rsubEmpty,normInitial []⟩
def rmInitial (input : List Bool) : RMData :=
  ⟨[],[],[],input,[],[],[],rmulEmpty,rsubEmpty,normInitial []⟩
def rmFinal (output : List Bool) : RMData :=
  ⟨[],[],[],[],[],[],[],rmulEmpty,rsubEmpty,normFinal output⟩

def rmMulEmbedding : MulStack ↪ RMStack := ⟨RMStack.multiply,fun _ _ h => RMStack.multiply.inj h⟩
def rmSubEmbedding : Option Bool ↪ RMStack := ⟨RMStack.subtract,fun _ _ h => RMStack.subtract.inj h⟩
def rmNormEmbedding : NormStack ↪ RMStack := ⟨RMStack.normalize,fun _ _ h => RMStack.normalize.inj h⟩

abbrev RMStmt := Stmt (fun _ : RMStack => Bool) RMLabel AddState

def rmPop (k : RMStack) (q : RMStmt) : RMStmt := .pop k (fun _ b => (false,b,none)) q

def rmGoto (next : RMPhase) : RMStmt := .load (fun _ => (false,none,none)) (.goto (fun _ => .work next))

def rmMove (src dst : RMStack) (again next : RMPhase) : RMStmt :=
  rmPop src <| .branch (fun v => v.2.1.isSome)
    (.push dst (fun v => v.2.1.getD false) (.goto (fun _ => .work again)))
    (.goto (fun _ => .work next))

def rmParse (src : RMStack) (again next : RMPhase) : RMStmt :=
  rmPop src <| .branch (fun v => v.2.1.getD false)
    (rmPop src <| .push (.work .tmp) (fun v => v.2.1.getD false) (.goto (fun _ => .work again)))
    (.goto (fun _ => .work next))

def rmFrame (dst : RMStack) (again : RMPhase) (next : RMLabel) : RMStmt :=
  rmPop (.work .tmp) <| .branch (fun v => v.2.1.isSome)
    (.push dst (fun v => v.2.1.getD false) <| .push dst (fun _ => true) (.goto (fun _ => .work again)))
    (.goto (fun _ => next))

def rmRead (src dst : RMStack) (next : RMPhase) : RMStmt :=
  rmPop src <| rmPop src <| rmPop src <| rmPop src <|
    .push dst (fun v => v.2.1.getD false) <| rmPop src <| rmPop src (.goto (fun _ => .work next))

def rmIncrement (src : RMStack) (again next : RMPhase) : RMStmt :=
  rmPop src <| .branch (fun v => v.2.1.getD false)
    (.push (.work .tmp) (fun _ => false) (.goto (fun _ => .work again)))
    (.push src (fun _ => true) (.goto (fun _ => .work next)))

def rmLocalProgram : RMPhase → RMStmt
  | .unframeFirst => rmParse (.work .db) .unframeFirst .restoreFirst
  | .restoreFirst => rmMove (.work .tmp) (.work .da) .restoreFirst .readA
  | .readA => rmRead (.work .da) (.work .sa) .parseA
  | .parseA => rmParse (.work .da) .parseA .restoreA
  | .restoreA => rmMove (.work .tmp) (.work .a) .restoreA .readB
  | .readB => rmRead (.work .db) (.work .sb) .parseB
  | .parseB => rmParse (.work .db) .parseB .restoreB
  | .restoreB => rmMove (.work .tmp) (.work .b) .restoreB .checkA
  | .checkA => .peek (.work .sa) (fun _ b => (false,b,none)) <|
      .branch (fun v => v.2.1.getD false) (rmGoto .incA) (rmGoto .checkB)
  | .incA => rmIncrement (.work .a) .incA .restoreIncA
  | .restoreIncA => rmMove (.work .tmp) (.work .a) .restoreIncA .checkB
  | .checkB => .peek (.work .sb) (fun _ b => (false,b,none)) <|
      .branch (fun v => v.2.1.getD false) (rmGoto .incB) (rmGoto .combineSigns)
  | .incB => rmIncrement (.work .b) .incB .restoreIncB
  | .restoreIncB => rmMove (.work .tmp) (.work .b) .restoreIncB .combineSigns
  | .combineSigns => .pop (.work .sa) (fun _ b => (b.getD false,none,none)) <|
      .pop (.work .sb) (fun v b => (xor v.1 (b.getD false),none,none)) <|
        .push (.work .sa) (fun v => v.1) (rmGoto .moveB)
  | .moveB => rmMove (.work .b) (.work .tmp) .moveB .inputB
  | .inputB => rmMove (.work .tmp) (.multiply .input) .inputB .numDelimiter
  | .numDelimiter => .push (.multiply .input) (fun _ => false) (.goto (fun _ => .work .reverseA))
  | .reverseA => rmMove (.work .a) (.work .tmp) .reverseA .frameNum
  | .frameNum => rmFrame (.multiply .input) .frameNum (.numMul .parse)
  | .afterNum => rmMove (.multiply .z) (.work .tmp) .afterNum .restoreProduct
  | .restoreProduct => rmMove (.work .tmp) (.work .a) .restoreProduct .checkProduct
  | .checkProduct => .peek (.work .a) (fun _ b => (false,b,none)) <|
      .branch (fun v => v.2.1.isSome)
        (.peek (.work .sa) (fun _ b => (false,b,none)) <|
          .branch (fun v => v.2.1.getD false) (rmGoto .predInput) (rmGoto .moveDenB))
        (rmPop (.work .sa) <| .push (.work .sa) (fun _ => false) (rmGoto .moveDenB))
  | .predInput => .push (.subtract none) (fun _ => true) <|
      .push (.subtract none) (fun _ => false) (.goto (fun _ => .work .reversePred))
  | .reversePred => rmMove (.work .a) (.work .tmp) .reversePred .framePred
  | .framePred => rmFrame (.subtract none) .framePred (.pred .parse)
  | .afterPred => rmMove (.subtract none) (.work .tmp) .afterPred .restorePred
  | .restorePred => rmMove (.work .tmp) (.work .a) .restorePred .moveDenB
  | .moveDenB => rmMove (.work .db) (.work .tmp) .moveDenB .inputDenB
  | .inputDenB => rmMove (.work .tmp) (.multiply .input) .inputDenB .denDelimiter
  | .denDelimiter => .push (.multiply .input) (fun _ => false) (.goto (fun _ => .work .reverseDenA))
  | .reverseDenA => rmMove (.work .da) (.work .tmp) .reverseDenA .frameDen
  | .frameDen => rmFrame (.multiply .input) .frameDen (.denMul .parse)
  | .afterDen => rmMove (.multiply .z) (.work .tmp) .afterDen .inputNormDen
  | .inputNormDen => rmMove (.work .tmp) (.normalize (.work .den)) .inputNormDen .normDelimiter
  | .normDelimiter => .push (.normalize (.work .den)) (fun _ => false) (.goto (fun _ => .work .reverseProduct))
  | .reverseProduct => rmMove (.work .a) (.work .tmp) .reverseProduct .frameNormalize
  | .frameNormalize => rmFrame (.normalize (.work .den)) .frameNormalize (.work .normTag)
  | .normTag => rmPop (.work .sa) <|
      .push (.normalize (.work .den)) (fun _ => false) <| .push (.normalize (.work .den)) (fun _ => true) <|
      .push (.normalize (.work .den)) (fun v => v.2.1.getD false) <| .push (.normalize (.work .den)) (fun _ => true) <|
      .push (.normalize (.work .den)) (fun _ => true) <| .push (.normalize (.work .den)) (fun _ => true) <|
      .load (fun _ => (false,none,none)) (.goto (fun _ => .norm (.work .readSign)))
  | .done => .load (fun _ => (false,none,none)) .halt

def rationalMultiplicationMachine : FinTM2 where
  K := RMStack
  k₀ := .work .db
  k₁ := .normalize (.divide .out)
  Γ _ := Bool
  Λ := RMLabel
  main := .work .unframeFirst
  σ := AddState
  initialState := (false,none,none)
  m
    | .work l => rmLocalProgram l
    | .numMul l => compile rmMulEmbedding RMLabel.numMul (Equiv.refl AddState) (.work .afterNum) (multiplicationMachine.m l)
    | .denMul l => compile rmMulEmbedding RMLabel.denMul (Equiv.refl AddState) (.work .afterDen) (multiplicationMachine.m l)
    | .pred l => compile rmSubEmbedding RMLabel.pred (Equiv.refl AddState) (.work .afterPred) ((subtractionMachine false).m l)
    | .norm l => compile rmNormEmbedding RMLabel.norm (Equiv.refl AddState) (.work .done) (rationalNormalizationMachine.m l)

@[simp] theorem rmMachine_m_work (l : RMPhase) : rationalMultiplicationMachine.m (.work l)=rmLocalProgram l := rfl
@[simp] theorem rm_work_inj (j k : RMLocal) : @Eq rationalMultiplicationMachine.K (RMStack.work j) (RMStack.work k) ↔ j=k :=
  ⟨RMStack.work.inj,congrArg RMStack.work⟩
@[simp] theorem rm_multiply_inj (j k : MulStack) : @Eq rationalMultiplicationMachine.K (RMStack.multiply j) (RMStack.multiply k) ↔ j=k :=
  ⟨RMStack.multiply.inj,congrArg RMStack.multiply⟩
@[simp] theorem rm_subtract_inj (j k : Option Bool) : @Eq rationalMultiplicationMachine.K (RMStack.subtract j) (RMStack.subtract k) ↔ j=k :=
  ⟨RMStack.subtract.inj,congrArg RMStack.subtract⟩
@[simp] theorem rm_normalize_inj (j k : NormStack) : @Eq rationalMultiplicationMachine.K (RMStack.normalize j) (RMStack.normalize k) ↔ j=k :=
  ⟨RMStack.normalize.inj,congrArg RMStack.normalize⟩

def rmCfg (l : Option RMLabel) (v : AddState) (s : RMData) : rationalMultiplicationMachine.Cfg := ⟨l,v,s.stacks⟩

@[simp] theorem rm_step_restoreFirst_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreFirst)) v {s with tmp := b::as, da := bs}) =
      some (rmCfg (some (.work .restoreFirst)) (false,some b,none) {s with tmp := as, da := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_restoreFirst_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreFirst)) v {s with tmp := [], da := bs}) =
      some (rmCfg (some (.work .readA)) (false,none,none) {s with tmp := [], da := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_restoreFirst (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .restoreFirst)) v {s with tmp := as, da := bs})
      (some (rmCfg (some (.work .readA)) (false,none,none) {s with tmp := [], da := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_restoreFirst_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_restoreFirst_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_restoreA_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreA)) v {s with tmp := b::as, a := bs}) =
      some (rmCfg (some (.work .restoreA)) (false,some b,none) {s with tmp := as, a := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_restoreA_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreA)) v {s with tmp := [], a := bs}) =
      some (rmCfg (some (.work .readB)) (false,none,none) {s with tmp := [], a := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_restoreA (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .restoreA)) v {s with tmp := as, a := bs})
      (some (rmCfg (some (.work .readB)) (false,none,none) {s with tmp := [], a := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_restoreA_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_restoreA_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_restoreB_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreB)) v {s with tmp := b::as, b := bs}) =
      some (rmCfg (some (.work .restoreB)) (false,some b,none) {s with tmp := as, b := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_restoreB_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreB)) v {s with tmp := [], b := bs}) =
      some (rmCfg (some (.work .checkA)) (false,none,none) {s with tmp := [], b := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_restoreB (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .restoreB)) v {s with tmp := as, b := bs})
      (some (rmCfg (some (.work .checkA)) (false,none,none) {s with tmp := [], b := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_restoreB_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_restoreB_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_restoreIncA_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreIncA)) v {s with tmp := b::as, a := bs}) =
      some (rmCfg (some (.work .restoreIncA)) (false,some b,none) {s with tmp := as, a := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_restoreIncA_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreIncA)) v {s with tmp := [], a := bs}) =
      some (rmCfg (some (.work .checkB)) (false,none,none) {s with tmp := [], a := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_restoreIncA (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .restoreIncA)) v {s with tmp := as, a := bs})
      (some (rmCfg (some (.work .checkB)) (false,none,none) {s with tmp := [], a := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_restoreIncA_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_restoreIncA_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_restoreIncB_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreIncB)) v {s with tmp := b::as, b := bs}) =
      some (rmCfg (some (.work .restoreIncB)) (false,some b,none) {s with tmp := as, b := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_restoreIncB_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreIncB)) v {s with tmp := [], b := bs}) =
      some (rmCfg (some (.work .combineSigns)) (false,none,none) {s with tmp := [], b := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_restoreIncB (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .restoreIncB)) v {s with tmp := as, b := bs})
      (some (rmCfg (some (.work .combineSigns)) (false,none,none) {s with tmp := [], b := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_restoreIncB_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_restoreIncB_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_moveB_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .moveB)) v {s with b := b::as, tmp := bs}) =
      some (rmCfg (some (.work .moveB)) (false,some b,none) {s with b := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_moveB_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .moveB)) v {s with b := [], tmp := bs}) =
      some (rmCfg (some (.work .inputB)) (false,none,none) {s with b := [], tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_moveB (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .moveB)) v {s with b := as, tmp := bs})
      (some (rmCfg (some (.work .inputB)) (false,none,none) {s with b := [], tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_moveB_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_moveB_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_inputB_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .inputB)) v {s with tmp := b::as, mp := {s.mp with input := bs}}) =
      some (rmCfg (some (.work .inputB)) (false,some b,none) {s with tmp := as, mp := {s.mp with input := b::bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update,rm_multiply_inj]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_inputB_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .inputB)) v {s with tmp := [], mp := {s.mp with input := bs}}) =
      some (rmCfg (some (.work .numDelimiter)) (false,none,none) {s with tmp := [], mp := {s.mp with input := bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
def rm_inputB (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .inputB)) v {s with tmp := as, mp := {s.mp with input := bs}})
      (some (rmCfg (some (.work .numDelimiter)) (false,none,none) {s with tmp := [], mp := {s.mp with input := as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_inputB_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_inputB_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_reverseA_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .reverseA)) v {s with a := b::as, tmp := bs}) =
      some (rmCfg (some (.work .reverseA)) (false,some b,none) {s with a := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_reverseA_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .reverseA)) v {s with a := [], tmp := bs}) =
      some (rmCfg (some (.work .frameNum)) (false,none,none) {s with a := [], tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_reverseA (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .reverseA)) v {s with a := as, tmp := bs})
      (some (rmCfg (some (.work .frameNum)) (false,none,none) {s with a := [], tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_reverseA_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_reverseA_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_afterNum_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .afterNum)) v {s with mp := {s.mp with z := b::as}, tmp := bs}) =
      some (rmCfg (some (.work .afterNum)) (false,some b,none) {s with mp := {s.mp with z := as}, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update,rm_multiply_inj]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_afterNum_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .afterNum)) v {s with mp := {s.mp with z := []}, tmp := bs}) =
      some (rmCfg (some (.work .restoreProduct)) (false,none,none) {s with mp := {s.mp with z := []}, tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
def rm_afterNum (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .afterNum)) v {s with mp := {s.mp with z := as}, tmp := bs})
      (some (rmCfg (some (.work .restoreProduct)) (false,none,none) {s with mp := {s.mp with z := []}, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_afterNum_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_afterNum_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_restoreProduct_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreProduct)) v {s with tmp := b::as, a := bs}) =
      some (rmCfg (some (.work .restoreProduct)) (false,some b,none) {s with tmp := as, a := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_restoreProduct_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restoreProduct)) v {s with tmp := [], a := bs}) =
      some (rmCfg (some (.work .checkProduct)) (false,none,none) {s with tmp := [], a := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_restoreProduct (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .restoreProduct)) v {s with tmp := as, a := bs})
      (some (rmCfg (some (.work .checkProduct)) (false,none,none) {s with tmp := [], a := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_restoreProduct_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_restoreProduct_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_reversePred_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .reversePred)) v {s with a := b::as, tmp := bs}) =
      some (rmCfg (some (.work .reversePred)) (false,some b,none) {s with a := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_reversePred_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .reversePred)) v {s with a := [], tmp := bs}) =
      some (rmCfg (some (.work .framePred)) (false,none,none) {s with a := [], tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_reversePred (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .reversePred)) v {s with a := as, tmp := bs})
      (some (rmCfg (some (.work .framePred)) (false,none,none) {s with a := [], tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_reversePred_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_reversePred_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_afterPred_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .afterPred)) v {s with sp := {s.sp with input := b::as}, tmp := bs}) =
      some (rmCfg (some (.work .afterPred)) (false,some b,none) {s with sp := {s.sp with input := as}, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RSubStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update,rm_subtract_inj]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_afterPred_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .afterPred)) v {s with sp := {s.sp with input := []}, tmp := bs}) =
      some (rmCfg (some (.work .restorePred)) (false,none,none) {s with sp := {s.sp with input := []}, tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RSubStore.stacks,step,stepAux]
def rm_afterPred (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .afterPred)) v {s with sp := {s.sp with input := as}, tmp := bs})
      (some (rmCfg (some (.work .restorePred)) (false,none,none) {s with sp := {s.sp with input := []}, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_afterPred_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_afterPred_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_restorePred_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restorePred)) v {s with tmp := b::as, a := bs}) =
      some (rmCfg (some (.work .restorePred)) (false,some b,none) {s with tmp := as, a := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_restorePred_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .restorePred)) v {s with tmp := [], a := bs}) =
      some (rmCfg (some (.work .moveDenB)) (false,none,none) {s with tmp := [], a := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_restorePred (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .restorePred)) v {s with tmp := as, a := bs})
      (some (rmCfg (some (.work .moveDenB)) (false,none,none) {s with tmp := [], a := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_restorePred_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_restorePred_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_moveDenB_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .moveDenB)) v {s with db := b::as, tmp := bs}) =
      some (rmCfg (some (.work .moveDenB)) (false,some b,none) {s with db := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_moveDenB_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .moveDenB)) v {s with db := [], tmp := bs}) =
      some (rmCfg (some (.work .inputDenB)) (false,none,none) {s with db := [], tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_moveDenB (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .moveDenB)) v {s with db := as, tmp := bs})
      (some (rmCfg (some (.work .inputDenB)) (false,none,none) {s with db := [], tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_moveDenB_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_moveDenB_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_inputDenB_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .inputDenB)) v {s with tmp := b::as, mp := {s.mp with input := bs}}) =
      some (rmCfg (some (.work .inputDenB)) (false,some b,none) {s with tmp := as, mp := {s.mp with input := b::bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update,rm_multiply_inj]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_inputDenB_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .inputDenB)) v {s with tmp := [], mp := {s.mp with input := bs}}) =
      some (rmCfg (some (.work .denDelimiter)) (false,none,none) {s with tmp := [], mp := {s.mp with input := bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
def rm_inputDenB (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .inputDenB)) v {s with tmp := as, mp := {s.mp with input := bs}})
      (some (rmCfg (some (.work .denDelimiter)) (false,none,none) {s with tmp := [], mp := {s.mp with input := as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_inputDenB_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_inputDenB_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_reverseDenA_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .reverseDenA)) v {s with da := b::as, tmp := bs}) =
      some (rmCfg (some (.work .reverseDenA)) (false,some b,none) {s with da := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_reverseDenA_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .reverseDenA)) v {s with da := [], tmp := bs}) =
      some (rmCfg (some (.work .frameDen)) (false,none,none) {s with da := [], tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_reverseDenA (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .reverseDenA)) v {s with da := as, tmp := bs})
      (some (rmCfg (some (.work .frameDen)) (false,none,none) {s with da := [], tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_reverseDenA_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_reverseDenA_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_afterDen_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .afterDen)) v {s with mp := {s.mp with z := b::as}, tmp := bs}) =
      some (rmCfg (some (.work .afterDen)) (false,some b,none) {s with mp := {s.mp with z := as}, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update,rm_multiply_inj]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_afterDen_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .afterDen)) v {s with mp := {s.mp with z := []}, tmp := bs}) =
      some (rmCfg (some (.work .inputNormDen)) (false,none,none) {s with mp := {s.mp with z := []}, tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
def rm_afterDen (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .afterDen)) v {s with mp := {s.mp with z := as}, tmp := bs})
      (some (rmCfg (some (.work .inputNormDen)) (false,none,none) {s with mp := {s.mp with z := []}, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_afterDen_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_afterDen_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_inputNormDen_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .inputNormDen)) v {s with tmp := b::as, np := {s.np with den := bs}}) =
      some (rmCfg (some (.work .inputNormDen)) (false,some b,none) {s with tmp := as, np := {s.np with den := b::bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,NormData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update,rm_normalize_inj]
@[simp] theorem rm_step_inputNormDen_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .inputNormDen)) v {s with tmp := [], np := {s.np with den := bs}}) =
      some (rmCfg (some (.work .normDelimiter)) (false,none,none) {s with tmp := [], np := {s.np with den := bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,NormData.stacks,step,stepAux]
def rm_inputNormDen (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .inputNormDen)) v {s with tmp := as, np := {s.np with den := bs}})
      (some (rmCfg (some (.work .normDelimiter)) (false,none,none) {s with tmp := [], np := {s.np with den := as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_inputNormDen_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_inputNormDen_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_reverseProduct_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .reverseProduct)) v {s with a := b::as, tmp := bs}) =
      some (rmCfg (some (.work .reverseProduct)) (false,some b,none) {s with a := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_reverseProduct_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .reverseProduct)) v {s with a := [], tmp := bs}) =
      some (rmCfg (some (.work .frameNormalize)) (false,none,none) {s with a := [], tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmMove,rmPop,rmCfg,RMData.stacks,step,stepAux]
def rm_reverseProduct (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .reverseProduct)) v {s with a := as, tmp := bs})
      (some (rmCfg (some (.work .frameNormalize)) (false,none,none) {s with a := [], tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa using oneStep rationalMultiplicationMachine.step (rm_step_reverseProduct_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_reverseProduct_cons v s b as bs))
      (ih (false,some b,none) (b::bs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using h


def rmMulLabels (denominator : Bool) : MulLabel → RMLabel := if denominator then RMLabel.denMul else RMLabel.numMul
def rmMulReturn (denominator : Bool) : RMLabel := .work (if denominator then .afterDen else .afterNum)

def rm_call_mul (denominator : Bool) (s : RMData) (a b : ℕ) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (rmMulLabels denominator .parse)) (false,none,none)
        {s with mp := {rmulEmpty with input := Complexity.BitEncoding.frame (Computability.encodeNat a) ++ Computability.encodeNat b}})
      (some (rmCfg (some (rmMulReturn denominator)) (false,none,none)
        {s with mp := {rmulEmpty with z := Computability.encodeNat (a*b)}}))
      (let N := (Complexity.BitEncoding.frame (Computability.encodeNat a) ++ Computability.encodeNat b).length
       (6*N+6)*N+3*N+4) := by
  have hs := multiplication_outputs_polynomial (Computability.encodeNat a) (Computability.encodeNat b)
  rw [mulBits_encodeNat] at hs
  apply PlanarHom.ReturningBitSubroutine.run rmMulEmbedding (rmMulLabels denominator)
    (Equiv.refl AddState) (rmMulReturn denominator) s.stacks multiplicationMachine.m rationalMultiplicationMachine.m
    (by intro l; cases denominator <;> rfl) _ _ _ _ _ hs
  · refine ⟨?_,rfl,?_,?_⟩
    · cases denominator <;> rfl
    · intro k; cases k <;> rfl
    · intro j hj; cases j with
      | work k => cases k <;> rfl
      | multiply k => exact False.elim (hj k rfl)
      | subtract k => rfl
      | normalize k => rfl
  · refine ⟨rfl,rfl,?_,?_⟩
    · intro k; cases k <;> rfl
    · intro j hj; cases j with
      | work k => cases k <;> rfl
      | multiply k => exact False.elim (hj k rfl)
      | subtract k => rfl
      | normalize k => rfl

def rm_call_pred (s : RMData) (n : ℕ) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.pred .parse)) (false,none,none)
        {s with sp := {rsubEmpty with input := Complexity.BitEncoding.frame (Computability.encodeNat n) ++ [true]}})
      (some (rmCfg (some (.work .afterPred)) (false,none,none)
        {s with sp := {rsubEmpty with input := Computability.encodeNat (n-1)}}))
      (4*(Computability.encodeNat n).length+6) := by
  have hs := subtraction_outputs false (Computability.encodeNat n) (Computability.encodeNat 1)
  have he : subtractionResult false
      (subtractWithBorrow false (Computability.encodeNat n) (Computability.encodeNat 1)).1
      (subtractWithBorrow false (Computability.encodeNat n) (Computability.encodeNat 1)).2 =
      Computability.encodeNat (n-1) := subBits_encodeNat n 1
  rw [he] at hs
  have h1 : Computability.encodeNat 1 = [true] := by
    simp [Computability.encodeNat,Computability.encodeNum,Computability.encodePosNum]
  have hs' : TM2OutputsInTime (subtractionMachine false)
      (Complexity.BitEncoding.frame (Computability.encodeNat n) ++ [true])
      (some (Computability.encodeNat (n-1))) (4*(Computability.encodeNat n).length+6) := by
    simpa only [h1,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.mul_one,Nat.add_assoc] using hs
  apply PlanarHom.ReturningBitSubroutine.run rmSubEmbedding RMLabel.pred (Equiv.refl AddState)
    (.work .afterPred) s.stacks (subtractionMachine false).m rationalMultiplicationMachine.m
    (fun _ => rfl) _ _ _ _ _ hs'
  · refine ⟨rfl,rfl,?_,?_⟩
    · intro k; rcases k with _ | (_ | _) <;> rfl
    · intro j hj; cases j with
      | work k => cases k <;> rfl
      | multiply k => rfl
      | subtract k => exact False.elim (hj k rfl)
      | normalize k => rfl
  · refine ⟨rfl,rfl,?_,?_⟩
    · intro k; rcases k with _ | (_ | _) <;> rfl
    · intro j hj; cases j with
      | work k => cases k <;> rfl
      | multiply k => rfl
      | subtract k => exact False.elim (hj k rfl)
      | normalize k => rfl

def rm_call_normalize (s : RMData) (sign : Bool) (n d : ℕ) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.norm (.work .readSign))) (false,none,none)
        {s with np := normInitial (ratWord sign (Computability.encodeNat n) (Computability.encodeNat d))})
      (some (rmCfg (some (.work .done)) (false,none,none)
        {s with np := normFinal (Complexity.BitEncoding.rat.encode (mkRat (signedIndex sign n) d))}))
      (let N := (ratWord sign (Computability.encodeNat n) (Computability.encodeNat d)).length
       3888*N^3+17442*N^2+26220*N+13258) := by
  have hs := rationalNormalization_outputs sign n d
  simp only [encode_int_nat_pair] at hs
  apply PlanarHom.ReturningBitSubroutine.run rmNormEmbedding RMLabel.norm (Equiv.refl AddState)
    (.work .done) s.stacks rationalNormalizationMachine.m rationalMultiplicationMachine.m
    (fun _ => rfl) _ _ _ _ _ hs
  · refine ⟨rfl,rfl,?_,?_⟩
    · intro k; cases k with
      | work k => cases k <;> rfl
      | gcd k => rcases k with k | k <;> cases k <;> rfl
      | divide k => cases k <;> rfl
    · intro j hj; cases j with
      | work k => cases k <;> rfl
      | multiply k => rfl
      | subtract k => rfl
      | normalize k => exact False.elim (hj k rfl)
  · refine ⟨rfl,rfl,?_,?_⟩
    · intro k; cases k with
      | work k => cases k <;> rfl
      | gcd k => rcases k with k | k <;> cases k <;> rfl
      | divide k => cases k <;> rfl
    · intro j hj; cases j with
      | work k => cases k <;> rfl
      | multiply k => rfl
      | subtract k => rfl
      | normalize k => exact False.elim (hj k rfl)

@[simp] theorem rm_step_unframeFirst_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .unframeFirst)) v {s with db := true::b::as, tmp := bs}) =
      some (rmCfg (some (.work .unframeFirst)) (false,some b,none) {s with db := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmParse,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_unframeFirst_end (v : AddState) (s : RMData) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .unframeFirst)) v {s with db := false::as, tmp := bs}) =
      some (rmCfg (some (.work .restoreFirst)) (false,some false,none) {s with db := as, tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmParse,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
def rm_unframeFirst (v : AddState) (s : RMData) (as tail bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .unframeFirst)) v {s with db := Complexity.BitEncoding.frame as ++ tail, tmp := bs})
      (some (rmCfg (some (.work .restoreFirst)) (false,some false,none) {s with db := tail, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [Complexity.BitEncoding.frame] using oneStep rationalMultiplicationMachine.step (rm_step_unframeFirst_end v s tail bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step
      (rm_step_unframeFirst_cons v s b (Complexity.BitEncoding.frame as ++ tail) bs)) (ih (false,some b,none) (b::bs))
    simpa [Complexity.BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_parseA_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .parseA)) v {s with da := true::b::as, tmp := bs}) =
      some (rmCfg (some (.work .parseA)) (false,some b,none) {s with da := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmParse,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_parseA_end (v : AddState) (s : RMData) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .parseA)) v {s with da := false::as, tmp := bs}) =
      some (rmCfg (some (.work .restoreA)) (false,some false,none) {s with da := as, tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmParse,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
def rm_parseA (v : AddState) (s : RMData) (as tail bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .parseA)) v {s with da := Complexity.BitEncoding.frame as ++ tail, tmp := bs})
      (some (rmCfg (some (.work .restoreA)) (false,some false,none) {s with da := tail, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [Complexity.BitEncoding.frame] using oneStep rationalMultiplicationMachine.step (rm_step_parseA_end v s tail bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step
      (rm_step_parseA_cons v s b (Complexity.BitEncoding.frame as ++ tail) bs)) (ih (false,some b,none) (b::bs))
    simpa [Complexity.BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_parseB_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .parseB)) v {s with db := true::b::as, tmp := bs}) =
      some (rmCfg (some (.work .parseB)) (false,some b,none) {s with db := as, tmp := b::bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmParse,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_parseB_end (v : AddState) (s : RMData) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .parseB)) v {s with db := false::as, tmp := bs}) =
      some (rmCfg (some (.work .restoreB)) (false,some false,none) {s with db := as, tmp := bs}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmParse,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
def rm_parseB (v : AddState) (s : RMData) (as tail bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .parseB)) v {s with db := Complexity.BitEncoding.frame as ++ tail, tmp := bs})
      (some (rmCfg (some (.work .restoreB)) (false,some false,none) {s with db := tail, tmp := as.reverse++bs})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [Complexity.BitEncoding.frame] using oneStep rationalMultiplicationMachine.step (rm_step_parseB_end v s tail bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step
      (rm_step_parseB_cons v s b (Complexity.BitEncoding.frame as ++ tail) bs)) (ih (false,some b,none) (b::bs))
    simpa [Complexity.BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_frameNum_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .frameNum)) v {s with tmp := b::as, mp := {s.mp with input := bs}}) =
      some (rmCfg (some (.work .frameNum)) (false,some b,none) {s with tmp := as, mp := {s.mp with input := true::b::bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmFrame,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update,rm_multiply_inj]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_frameNum_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .frameNum)) v {s with tmp := [], mp := {s.mp with input := bs}}) =
      some (rmCfg (some (.numMul .parse)) (false,none,none) {s with tmp := [], mp := {s.mp with input := bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmFrame,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
def rm_frameNum (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .frameNum)) v {s with tmp := as, mp := {s.mp with input := bs}})
      (some (rmCfg (some (.numMul .parse)) (false,none,none) {s with tmp := [], mp := {s.mp with input := framePrefix as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep rationalMultiplicationMachine.step (rm_step_frameNum_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_frameNum_cons v s b as bs))
      (ih (false,some b,none) (true::b::bs))
    simpa [List.reverse_cons,framePrefix,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_framePred_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .framePred)) v {s with tmp := b::as, sp := {s.sp with input := bs}}) =
      some (rmCfg (some (.work .framePred)) (false,some b,none) {s with tmp := as, sp := {s.sp with input := true::b::bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmFrame,rmPop,rmCfg,RMData.stacks,RSubStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update,rm_subtract_inj]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_framePred_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .framePred)) v {s with tmp := [], sp := {s.sp with input := bs}}) =
      some (rmCfg (some (.pred .parse)) (false,none,none) {s with tmp := [], sp := {s.sp with input := bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmFrame,rmPop,rmCfg,RMData.stacks,RSubStore.stacks,step,stepAux]
def rm_framePred (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .framePred)) v {s with tmp := as, sp := {s.sp with input := bs}})
      (some (rmCfg (some (.pred .parse)) (false,none,none) {s with tmp := [], sp := {s.sp with input := framePrefix as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep rationalMultiplicationMachine.step (rm_step_framePred_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_framePred_cons v s b as bs))
      (ih (false,some b,none) (true::b::bs))
    simpa [List.reverse_cons,framePrefix,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_frameDen_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .frameDen)) v {s with tmp := b::as, mp := {s.mp with input := bs}}) =
      some (rmCfg (some (.work .frameDen)) (false,some b,none) {s with tmp := as, mp := {s.mp with input := true::b::bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmFrame,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update,rm_multiply_inj]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]
@[simp] theorem rm_step_frameDen_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .frameDen)) v {s with tmp := [], mp := {s.mp with input := bs}}) =
      some (rmCfg (some (.denMul .parse)) (false,none,none) {s with tmp := [], mp := {s.mp with input := bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmFrame,rmPop,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
def rm_frameDen (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .frameDen)) v {s with tmp := as, mp := {s.mp with input := bs}})
      (some (rmCfg (some (.denMul .parse)) (false,none,none) {s with tmp := [], mp := {s.mp with input := framePrefix as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep rationalMultiplicationMachine.step (rm_step_frameDen_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_frameDen_cons v s b as bs))
      (ih (false,some b,none) (true::b::bs))
    simpa [List.reverse_cons,framePrefix,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_frameNormalize_cons (v : AddState) (s : RMData) (b : Bool) (as bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .frameNormalize)) v {s with tmp := b::as, np := {s.np with den := bs}}) =
      some (rmCfg (some (.work .frameNormalize)) (false,some b,none) {s with tmp := as, np := {s.np with den := true::b::bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmFrame,rmPop,rmCfg,RMData.stacks,NormData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update,rm_normalize_inj]
@[simp] theorem rm_step_frameNormalize_nil (v : AddState) (s : RMData) (bs : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .frameNormalize)) v {s with tmp := [], np := {s.np with den := bs}}) =
      some (rmCfg (some (.work .normTag)) (false,none,none) {s with tmp := [], np := {s.np with den := bs}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmFrame,rmPop,rmCfg,RMData.stacks,NormData.stacks,step,stepAux]
def rm_frameNormalize (v : AddState) (s : RMData) (as bs : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .frameNormalize)) v {s with tmp := as, np := {s.np with den := bs}})
      (some (rmCfg (some (.work .normTag)) (false,none,none) {s with tmp := [], np := {s.np with den := framePrefix as.reverse++bs}})) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [framePrefix] using oneStep rationalMultiplicationMachine.step (rm_step_frameNormalize_nil v s bs)
  | cons b as ih =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_frameNormalize_cons v s b as bs))
      (ih (false,some b,none) (true::b::bs))
    simpa [List.reverse_cons,framePrefix,List.append_assoc,Nat.add_comm] using h

@[simp] theorem rm_step_readA (v : AddState) (s : RMData) (sign : Bool) (as ds : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .readA)) v {s with da := ratWord sign as ds, sa := []}) =
      some (rmCfg (some (.work .parseA)) (false,some false,none) {s with da := Complexity.BitEncoding.frame as ++ ds, sa := [sign]}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmRead,rmPop,rmCfg,ratWord,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

@[simp] theorem rm_step_readB (v : AddState) (s : RMData) (sign : Bool) (as ds : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .readB)) v {s with db := ratWord sign as ds, sb := []}) =
      some (rmCfg (some (.work .parseB)) (false,some false,none) {s with db := Complexity.BitEncoding.frame as ++ ds, sb := [sign]}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmRead,rmPop,rmCfg,ratWord,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

@[simp] theorem rm_step_numDelimiter (v : AddState) (s : RMData) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .numDelimiter)) v s) =
      some (rmCfg (some (.work .reverseA)) v {s with mp := {s.mp with input := false :: s.mp.input}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update,rm_multiply_inj]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

@[simp] theorem rm_step_denDelimiter (v : AddState) (s : RMData) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .denDelimiter)) v s) =
      some (rmCfg (some (.work .reverseDenA)) v {s with mp := {s.mp with input := false :: s.mp.input}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmCfg,RMData.stacks,RMulStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update,rm_multiply_inj]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

@[simp] theorem rm_step_normDelimiter (v : AddState) (s : RMData) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .normDelimiter)) v s) =
      some (rmCfg (some (.work .reverseProduct)) v {s with np := {s.np with den := false :: s.np.den}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmCfg,RMData.stacks,NormData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update,rm_normalize_inj]

@[simp] theorem rm_step_incA_true (v : AddState) (s : RMData) (xs ys : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .incA)) v {s with a := true::xs, tmp := ys}) =
      some (rmCfg (some (.work .incA)) (false,some true,none) {s with a := xs, tmp := false::ys}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmIncrement,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

@[simp] theorem rm_step_incA_false (v : AddState) (s : RMData) (xs ys : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .incA)) v {s with a := false::xs, tmp := ys}) =
      some (rmCfg (some (.work .restoreIncA)) (false,some false,none) {s with a := true::xs, tmp := ys}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmIncrement,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

@[simp] theorem rm_step_incA_nil (v : AddState) (s : RMData) (ys : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .incA)) v {s with a := [], tmp := ys}) =
      some (rmCfg (some (.work .restoreIncA)) (false,none,none) {s with a := [true], tmp := ys}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmIncrement,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

def rm_incA (v : AddState) (s : RMData) (xs ys : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .incA)) v {s with a := xs, tmp := ys})
      (some (rmCfg (some (.work .checkB)) (false,none,none) {s with a := ys.reverse++succBits xs, tmp := []})) (2*xs.length+ys.length+2) := by
  induction xs generalizing v ys with
  | nil =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_incA_nil v s ys))
      (rm_restoreIncA (false,none,none) s ys [true])
    have ht : 1+(ys.length+1)=ys.length+2 := by omega
    rw [ht] at h
    simpa [succBits] using h
  | cons b xs ih =>
    cases b with
    | false =>
      have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_incA_false v s xs ys))
        (rm_restoreIncA (false,some false,none) s ys (true::xs))
      apply weakenTime (by simpa [succBits] using h)
      simp; omega
    | true =>
      have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_incA_true v s xs ys))
        (ih (false,some true,none) (false::ys))
      have ht : 1+(2*xs.length+(false::ys).length+2)=2*(true::xs).length+ys.length+2 := by simp;omega
      rw [ht] at h
      simpa [succBits,List.reverse_cons,List.append_assoc] using h

@[simp] theorem rm_step_checkA (v : AddState) (s : RMData) (sign : Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .checkA)) v {s with sa := [sign]}) =
      some (rmCfg (some (.work (if sign then .incA else .checkB))) (false,none,none) {s with sa := [sign]}) := by
  cases sign <;> simp [rmMachine_m_work,rmLocalProgram,rmGoto,rmCfg,RMData.stacks,step,stepAux]

@[simp] theorem rm_step_incB_true (v : AddState) (s : RMData) (xs ys : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .incB)) v {s with b := true::xs, tmp := ys}) =
      some (rmCfg (some (.work .incB)) (false,some true,none) {s with b := xs, tmp := false::ys}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmIncrement,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

@[simp] theorem rm_step_incB_false (v : AddState) (s : RMData) (xs ys : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .incB)) v {s with b := false::xs, tmp := ys}) =
      some (rmCfg (some (.work .restoreIncB)) (false,some false,none) {s with b := true::xs, tmp := ys}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmIncrement,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

@[simp] theorem rm_step_incB_nil (v : AddState) (s : RMData) (ys : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .incB)) v {s with b := [], tmp := ys}) =
      some (rmCfg (some (.work .restoreIncB)) (false,none,none) {s with b := [true], tmp := ys}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmIncrement,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => cases k <;> simp [RMData.stacks,RMulStore.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update]
    | divide k => cases k <;> simp [RMData.stacks,NormData.stacks,DivData.stacks,Function.update]

def rm_incB (v : AddState) (s : RMData) (xs ys : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step (rmCfg (some (.work .incB)) v {s with b := xs, tmp := ys})
      (some (rmCfg (some (.work .combineSigns)) (false,none,none) {s with b := ys.reverse++succBits xs, tmp := []})) (2*xs.length+ys.length+2) := by
  induction xs generalizing v ys with
  | nil =>
    have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_incB_nil v s ys))
      (rm_restoreIncB (false,none,none) s ys [true])
    have ht : 1+(ys.length+1)=ys.length+2 := by omega
    rw [ht] at h
    simpa [succBits] using h
  | cons b xs ih =>
    cases b with
    | false =>
      have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_incB_false v s xs ys))
        (rm_restoreIncB (false,some false,none) s ys (true::xs))
      apply weakenTime (by simpa [succBits] using h)
      simp; omega
    | true =>
      have h := normSeq (oneStep rationalMultiplicationMachine.step (rm_step_incB_true v s xs ys))
        (ih (false,some true,none) (false::ys))
      have ht : 1+(2*xs.length+(false::ys).length+2)=2*(true::xs).length+ys.length+2 := by simp;omega
      rw [ht] at h
      simpa [succBits,List.reverse_cons,List.append_assoc] using h

@[simp] theorem rm_step_checkB (v : AddState) (s : RMData) (sign : Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .checkB)) v {s with sb := [sign]}) =
      some (rmCfg (some (.work (if sign then .incB else .combineSigns))) (false,none,none) {s with sb := [sign]}) := by
  cases sign <;> simp [rmMachine_m_work,rmLocalProgram,rmGoto,rmCfg,RMData.stacks,step,stepAux]


@[simp] theorem rm_step_combineSigns (v : AddState) (s : RMData) (sa sb : Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .combineSigns)) v {s with sa := [sa],sb := [sb]}) =
      some (rmCfg (some (.work .moveB)) (false,none,none) {s with sa := [xor sa sb],sb := []}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmGoto,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => simp [RMData.stacks,Function.update]
  | subtract k => simp [RMData.stacks,Function.update]
  | normalize k => simp [RMData.stacks,Function.update]

@[simp] theorem rm_step_checkProduct_nil (v : AddState) (s : RMData) (sign : Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .checkProduct)) v {s with a := [],sa := [sign]}) =
      some (rmCfg (some (.work .moveDenB)) (false,none,none) {s with a := [],sa := [false]}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmGoto,rmPop,rmCfg,RMData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => simp [RMData.stacks,Function.update]
  | subtract k => simp [RMData.stacks,Function.update]
  | normalize k => simp [RMData.stacks,Function.update]

@[simp] theorem rm_step_checkProduct_nonempty (v : AddState) (s : RMData) (sign : Bool)
    (as : List Bool) (ha : as ≠ []) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .checkProduct)) v {s with a := as,sa := [sign]}) =
      some (rmCfg (some (.work (if sign then .predInput else .moveDenB))) (false,none,none)
        {s with a := as,sa := [sign]}) := by
  cases as with
  | nil => contradiction
  | cons b as => cases sign <;> simp [rmMachine_m_work,rmLocalProgram,rmGoto,rmCfg,RMData.stacks,step,stepAux]

@[simp] theorem rm_step_predInput (v : AddState) (s : RMData) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .predInput)) v {s with sp := {s.sp with input := []}}) =
      some (rmCfg (some (.work .reversePred)) v {s with sp := {s.sp with input := [false,true]}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmCfg,RMData.stacks,RSubStore.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update]
  | multiply k => simp [RMData.stacks,Function.update]
  | subtract k => rcases k with _ | (_ | _) <;> simp [RMData.stacks,RSubStore.stacks,Function.update,rm_subtract_inj]
  | normalize k => simp [RMData.stacks,Function.update]

@[simp] theorem rm_step_normTag (v : AddState) (s : RMData) (sign : Bool) (out : List Bool) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .normTag)) v
      {s with sa := [sign],np := {s.np with den := out}}) =
      some (rmCfg (some (.norm (.work .readSign))) (false,none,none)
        {s with sa := [],np := {s.np with den := [true,true,true,sign,true,false] ++ out}}) := by
  simp [rmMachine_m_work,rmLocalProgram,rmPop,rmCfg,RMData.stacks,NormData.stacks,step,stepAux]
  funext k; cases k with
  | work k => cases k <;> simp [RMData.stacks,Function.update,rm_work_inj]
  | multiply k => simp [RMData.stacks,Function.update]
  | subtract k => simp [RMData.stacks,Function.update]
  | normalize k => cases k with
    | work k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]
    | gcd k => cases k <;> simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]
    | divide k => simp [RMData.stacks,NormData.stacks,Function.update,rm_normalize_inj]

@[simp] theorem rm_step_done (v : AddState) (s : RMData) :
    rationalMultiplicationMachine.step (rmCfg (some (.work .done)) v s) =
      some (rmCfg none (false,none,none) s) := by
  simp [rmMachine_m_work,rmLocalProgram,rmCfg,step,stepAux]

def rm_parse_inputs (v : AddState) (sa sb : Bool) (as bs da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .unframeFirst)) v
        (rmInitial (Complexity.BitEncoding.frame (ratWord sa as da) ++ ratWord sb bs db)))
      (some (rmCfg (some (.work .checkA)) (false,none,none) (rmReady sa sb as bs da db)))
      (2*(ratWord sa as da).length+2*as.length+2*bs.length+8) := by
  let qa := ratWord sa as da
  let qb := ratWord sb bs db
  have h1 := rm_unframeFirst v (rmInitial qb) qa qb []
  have h2 := rm_restoreFirst (false,some false,none) (rmInitial qb) qa.reverse []
  have h3 := oneStep rationalMultiplicationMachine.step (rm_step_readA (false,none,none) (rmInitial qb) sa as da)
  have h4 := rm_parseA (false,some false,none) {rmInitial qb with sa := [sa]} as da []
  have h5 := rm_restoreA (false,some false,none) {rmInitial qb with sa := [sa],da := da} as.reverse []
  have h6 := oneStep rationalMultiplicationMachine.step
    (rm_step_readB (false,none,none) {rmInitial qb with sa := [sa],da := da,a := as} sb bs db)
  have h7 := rm_parseB (false,some false,none) (rmReady sa sb as [] da db) bs db []
  have h8 := rm_restoreB (false,some false,none) (rmReady sa sb as [] da db) bs.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2 h4 h5 h7 h8
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 (normSeq h5 (normSeq h6 (normSeq h7 h8))))))
  have ht : (qa.length+1)+((qa.length+1)+(1+((as.length+1)+((as.length+1)+(1+((bs.length+1)+(bs.length+1))))))) =
      2*qa.length+2*as.length+2*bs.length+8 := by omega
  rw [ht] at h
  exact h

def rm_magnitudeA (v : AddState) (sa sb : Bool) (as bs da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .checkA)) v (rmReady sa sb as bs da db))
      (some (rmCfg (some (.work .checkB)) (false,none,none)
        (rmReady sa sb (if sa then succBits as else as) bs da db))) (2*as.length+3) := by
  have hs := oneStep rationalMultiplicationMachine.step (rm_step_checkA v (rmReady sa sb as bs da db) sa)
  cases sa with
  | false => apply weakenTime hs; omega
  | true =>
    have hi := rm_incA (false,none,none) (rmReady true sb as bs da db) as []
    simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.add_zero] at hi
    have h := normSeq hs hi
    have ht : 1+(2*as.length+2)=2*as.length+3 := by omega
    rw [ht] at h
    exact h

def rm_magnitudeB (v : AddState) (sa sb : Bool) (as bs da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .checkB)) v (rmReady sa sb as bs da db))
      (some (rmCfg (some (.work .combineSigns)) (false,none,none)
        (rmReady sa sb as (if sb then succBits bs else bs) da db))) (2*bs.length+3) := by
  have hs := oneStep rationalMultiplicationMachine.step (rm_step_checkB v (rmReady sa sb as bs da db) sb)
  cases sb with
  | false => apply weakenTime hs; omega
  | true =>
    have hi := rm_incB (false,none,none) (rmReady sa true as bs da db) bs []
    simp only [List.reverse_nil,List.nil_append,List.length_nil,Nat.add_zero] at hi
    have h := normSeq hs hi
    have ht : 1+(2*bs.length+2)=2*bs.length+3 := by omega
    rw [ht] at h
    exact h

def rm_prepare_num (v : AddState) (sign : Bool) (as bs da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .moveB)) v (rmSigned sign as bs da db))
      (some (rmCfg (some (.numMul .parse)) (false,none,none)
        {rmSigned sign [] [] da db with mp := {rmulEmpty with input := Complexity.BitEncoding.frame as ++ bs}}))
      (2*as.length+2*bs.length+5) := by
  let s := rmSigned sign as bs da db
  have h1 := rm_moveB v s bs []
  have h2 := rm_inputB (false,none,none) {s with b := []} bs.reverse []
  have h3 := oneStep rationalMultiplicationMachine.step
    (rm_step_numDelimiter (false,none,none) {s with b := [],mp := {rmulEmpty with input := bs}})
  have h4 := rm_reverseA (false,none,none) {s with b := [],mp := {rmulEmpty with input := false::bs}} as []
  have h5 := rm_frameNum (false,none,none) {s with a := [],b := []} as.reverse (false::bs)
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2 h4 h5
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 h5)))
  have ht : (bs.length+1)+((bs.length+1)+(1+((as.length+1)+(as.length+1))))=2*as.length+2*bs.length+5 := by omega
  rw [ht] at h
  simpa only [framePrefix_delimiter] using h

def rm_get_product (v : AddState) (sign : Bool) (ps da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .afterNum)) v {rmSigned sign [] [] da db with mp := {rmulEmpty with z := ps}})
      (some (rmCfg (some (.work .checkProduct)) (false,none,none) (rmSigned sign ps [] da db)))
      (2*ps.length+2) := by
  let s := rmSigned sign [] [] da db
  have h1 := rm_afterNum v s ps []
  have h2 := rm_restoreProduct (false,none,none) s ps.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2
  have h := normSeq h1 h2
  have ht : (ps.length+1)+(ps.length+1)=2*ps.length+2 := by omega
  rw [ht] at h
  exact h


def rm_prepare_pred (v : AddState) (sign : Bool) (ps da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .predInput)) v (rmSigned sign ps [] da db))
      (some (rmCfg (some (.pred .parse)) (false,none,none)
        {rmSigned sign [] [] da db with sp := {rsubEmpty with input := Complexity.BitEncoding.frame ps ++ [true]}}))
      (2*ps.length+3) := by
  let s := rmSigned sign ps [] da db
  have h1 := oneStep rationalMultiplicationMachine.step (rm_step_predInput v s)
  have h2 := rm_reversePred v {s with sp := {rsubEmpty with input := [false,true]}} ps []
  have h3 := rm_framePred (false,none,none) {s with a := []} ps.reverse [false,true]
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h2 h3
  have h := normSeq h1 (normSeq h2 h3)
  have ht : 1+((ps.length+1)+(ps.length+1))=2*ps.length+3 := by omega
  rw [ht] at h
  simpa only [framePrefix_delimiter] using h

def rm_get_pred (v : AddState) (sign : Bool) (ps da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .afterPred)) v {rmSigned sign [] [] da db with sp := {rsubEmpty with input := ps}})
      (some (rmCfg (some (.work .moveDenB)) (false,none,none) (rmSigned sign ps [] da db)))
      (2*ps.length+2) := by
  let s := rmSigned sign [] [] da db
  have h1 := rm_afterPred v s ps []
  have h2 := rm_restorePred (false,none,none) s ps.reverse []
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2
  have h := normSeq h1 h2
  have ht : (ps.length+1)+(ps.length+1)=2*ps.length+2 := by omega
  rw [ht] at h
  exact h

/-- Convert a sign/magnitude product back to the canonical constructor-index
representation, using an actual subtraction call when negative. -/
def rm_adjust_product (v : AddState) (sign : Bool) (p : ℕ) (da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .checkProduct)) v (rmSigned sign (Computability.encodeNat p) [] da db))
      (some (rmCfg (some (.work .moveDenB)) (false,none,none)
        (rmSigned (if p=0 then false else sign)
          (Computability.encodeNat (if sign then p-1 else p)) [] da db)))
      (8*(Computability.encodeNat p).length+12) := by
  by_cases hp : p=0
  · subst p
    have h0 : Computability.encodeNat 0=[] := (encodeNat_eq_nil 0).2 rfl
    have h := oneStep rationalMultiplicationMachine.step
      (rm_step_checkProduct_nil v (rmSigned sign [] [] da db) sign)
    apply weakenTime (by simpa only [h0,Nat.sub_zero,Nat.zero_sub,ite_self,↓reduceIte] using h)
    omega
  · have hne : Computability.encodeNat p ≠ [] := by simpa using hp
    have h1 := oneStep rationalMultiplicationMachine.step
      (rm_step_checkProduct_nonempty v (rmSigned sign (Computability.encodeNat p) [] da db) sign
        (Computability.encodeNat p) hne)
    cases sign with
    | false =>
      apply weakenTime (by simpa only [hp,↓reduceIte] using h1)
      omega
    | true =>
      have h2 := rm_prepare_pred (false,none,none) true (Computability.encodeNat p) da db
      have h3 := rm_call_pred (rmSigned true [] [] da db) p
      have h4 := rm_get_pred (false,none,none) true (Computability.encodeNat (p-1)) da db
      have h := normSeq h1 (normSeq h2 (normSeq h3 h4))
      apply weakenTime (by simpa only [hp,↓reduceIte] using h)
      have hl := encodeNat_length_mono (Nat.sub_le p 1)
      omega

def rm_prepare_den (v : AddState) (sign : Bool) (ps da db : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .moveDenB)) v (rmSigned sign ps [] da db))
      (some (rmCfg (some (.denMul .parse)) (false,none,none)
        {rmSigned sign ps [] [] [] with mp := {rmulEmpty with input := Complexity.BitEncoding.frame da ++ db}}))
      (2*da.length+2*db.length+5) := by
  let s := rmSigned sign ps [] da db
  have h1 := rm_moveDenB v s db []
  have h2 := rm_inputDenB (false,none,none) {s with db := []} db.reverse []
  have h3 := oneStep rationalMultiplicationMachine.step
    (rm_step_denDelimiter (false,none,none) {s with db := [],mp := {rmulEmpty with input := db}})
  have h4 := rm_reverseDenA (false,none,none) {s with db := [],mp := {rmulEmpty with input := false::db}} da []
  have h5 := rm_frameDen (false,none,none) {s with da := [],db := []} da.reverse (false::db)
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at h1 h2 h4 h5
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 h5)))
  have ht : (db.length+1)+((db.length+1)+(1+((da.length+1)+(da.length+1))))=2*da.length+2*db.length+5 := by omega
  rw [ht] at h
  simpa only [framePrefix_delimiter] using h

def rm_prepare_normalize (v : AddState) (sign : Bool) (ps ds : List Bool) :
    EvalsToInTime rationalMultiplicationMachine.step
      (rmCfg (some (.work .afterDen)) v {rmSigned sign ps [] [] [] with mp := {rmulEmpty with z := ds}})
      (some (rmCfg (some (.norm (.work .readSign))) (false,none,none)
        {rmFinal [] with np := normInitial (ratWord sign ps ds)}))
      (2*ds.length+2*ps.length+6) := by
  let s := rmSigned sign ps [] [] []
  have h1 := rm_afterDen v s ds []
  have h2 := rm_inputNormDen (false,none,none) s ds.reverse []
  have h3 := oneStep rationalMultiplicationMachine.step
    (rm_step_normDelimiter (false,none,none) {s with np := normInitial ds})
  have h4 := rm_reverseProduct (false,none,none) {s with np := normInitial (false::ds)} ps []
  have h5 := rm_frameNormalize (false,none,none) {s with a := []} ps.reverse (false::ds)
  have h6 := oneStep rationalMultiplicationMachine.step
    (rm_step_normTag (false,none,none) (rmFinal []) sign (Complexity.BitEncoding.frame ps ++ ds))
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil,framePrefix_delimiter] at h1 h2 h4 h5
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 (normSeq h5 h6))))
  have ht : (ds.length+1)+((ds.length+1)+(1+((ps.length+1)+((ps.length+1)+1)))) =
      2*ds.length+2*ps.length+6 := by omega
  rw [ht] at h
  simpa only [ratWord,List.append_assoc] using h


def rmMulTime (n : ℕ) : ℕ := (6*n+6)*n+3*n+4
def rmNormTime (n : ℕ) : ℕ := 3888*n^3+17442*n^2+26220*n+13258
def rmTime (n : ℕ) : ℕ := rmNormTime (10*n+20)+2*rmMulTime (10*n+20)+100*n+100

/-- The complete multiplication computation on explicit signed numerator and
natural denominator words. Inputs need not already be reduced. -/
def rationalMultiplication_outputs (sa sb : Bool) (a b da db : ℕ) :
    TM2OutputsInTime rationalMultiplicationMachine
      (Complexity.BitEncoding.frame (ratWord sa (Computability.encodeNat a) (Computability.encodeNat da)) ++
        ratWord sb (Computability.encodeNat b) (Computability.encodeNat db))
      (some (Complexity.BitEncoding.rat.encode (mkRat (signedIndex sa a * signedIndex sb b) (da*db))))
      (rmTime (Complexity.BitEncoding.frame (ratWord sa (Computability.encodeNat a) (Computability.encodeNat da)) ++
        ratWord sb (Computability.encodeNat b) (Computability.encodeNat db)).length) := by
  let A := magnitudeIndex sa a
  let B := magnitudeIndex sb b
  let P := A*B
  let D := da*db
  let S := productSign sa sb P
  let I := productIndex sa sb P
  let as := Computability.encodeNat a
  let bs := Computability.encodeNat b
  let das := Computability.encodeNat da
  let dbs := Computability.encodeNat db
  let mas := Computability.encodeNat A
  let mbs := Computability.encodeNat B
  let ps := Computability.encodeNat P
  let ds := Computability.encodeNat D
  let is := Computability.encodeNat I
  let qa := ratWord sa as das
  let qb := ratWord sb bs dbs
  let N := (Complexity.BitEncoding.frame qa ++ qb).length
  have ha : (if sa then succBits as else as)=mas := by cases sa <;> simp [as,mas,A,magnitudeIndex]
  have hb : (if sb then succBits bs else bs)=mbs := by cases sb <;> simp [bs,mbs,B,magnitudeIndex]
  have hI : I=(if xor sa sb then P-1 else P) := by
    dsimp [I,productIndex,productSign]
    by_cases hp : P=0 <;> simp [hp]
  have hS : S=(if P=0 then false else xor sa sb) := rfl
  have h1 := rm_parse_inputs (false,none,none) sa sb as bs das dbs
  have h2 := rm_magnitudeA (false,none,none) sa sb as bs das dbs
  rw [ha] at h2
  have h3 := rm_magnitudeB (false,none,none) sa sb mas bs das dbs
  rw [hb] at h3
  have h4 := oneStep rationalMultiplicationMachine.step
    (rm_step_combineSigns (false,none,none) (rmReady sa sb mas mbs das dbs) sa sb)
  have h5 := rm_prepare_num (false,none,none) (xor sa sb) mas mbs das dbs
  have h6 := rm_call_mul false (rmSigned (xor sa sb) [] [] das dbs) A B
  have h7 := rm_get_product (false,none,none) (xor sa sb) ps das dbs
  have h8 := rm_adjust_product (false,none,none) (xor sa sb) P das dbs
  rw [← hS,← hI] at h8
  have h9 := rm_prepare_den (false,none,none) S is das dbs
  have h10 := rm_call_mul true (rmSigned S is [] [] []) da db
  have h11 := rm_prepare_normalize (false,none,none) S is ds
  have h12 := rm_call_normalize (rmFinal []) S I D
  have h13 := oneStep rationalMultiplicationMachine.step
    (rm_step_done (false,none,none) (rmFinal (Complexity.BitEncoding.rat.encode (mkRat (signedIndex S I) D))))
  have h := normSeq h1 (normSeq h2 (normSeq h3 (normSeq h4 (normSeq h5
    (normSeq h6 (normSeq h7 (normSeq h8 (normSeq h9 (normSeq h10 (normSeq h11 (normSeq h12 h13)))))))))))
  have hnum : signedIndex S I = signedIndex sa a * signedIndex sb b := signedIndex_product sa sb a b
  rw [hnum] at h
  have hi : initList rationalMultiplicationMachine (Complexity.BitEncoding.frame qa ++ qb) =
      rmCfg (some (.work .unframeFirst)) (false,none,none) (rmInitial (Complexity.BitEncoding.frame qa ++ qb)) := by
    unfold initList rmCfg rmInitial
    congr 1
    funext k; cases k with
    | work k => cases k <;> rfl
    | multiply k => cases k <;> rfl
    | subtract k => rcases k with _ | (_ | _) <;> rfl
    | normalize k => cases k with
      | work k => cases k <;> rfl
      | gcd k => rcases k with k | k <;> cases k <;> rfl
      | divide k => cases k <;> rfl
  have ho (out : List Bool) : haltList rationalMultiplicationMachine out =
      rmCfg none (false,none,none) (rmFinal out) := by
    unfold haltList rmCfg rmFinal
    congr 1
    funext k; cases k with
    | work k => cases k <;> rfl
    | multiply k => cases k <;> rfl
    | subtract k => rcases k with _ | (_ | _) <;> rfl
    | normalize k => cases k with
      | work k => cases k <;> rfl
      | gcd k => rcases k with k | k <;> cases k <;> rfl
      | divide k => cases k <;> rfl
  change EvalsToInTime rationalMultiplicationMachine.step
    (initList rationalMultiplicationMachine (Complexity.BitEncoding.frame qa ++ qb))
    (some (haltList rationalMultiplicationMachine
      (Complexity.BitEncoding.rat.encode (mkRat (signedIndex sa a * signedIndex sb b) D)))) (rmTime N)
  rw [hi,ho]
  apply weakenTime h
  have hbase : qa.length ≤ N ∧ as.length ≤ N ∧ bs.length ≤ N ∧ das.length ≤ N ∧ dbs.length ≤ N := by
    dsimp [N,qa,qb,ratWord]
    simp only [List.length_append,Complexity.BitEncoding.frame_length,List.length_cons]
    omega
  have hma : mas.length ≤ N+1 := by
    have hh : (if sa then succBits as else as).length ≤ as.length+1 := by
      cases sa with
      | false => simp
      | true => exact succBits_length_le as
    rw [ha] at hh
    omega
  have hmb : mbs.length ≤ N+1 := by
    have hh : (if sb then succBits bs else bs).length ≤ bs.length+1 := by
      cases sb with
      | false => simp
      | true => exact succBits_length_le bs
    rw [hb] at hh
    omega
  have hp : ps.length ≤ mas.length+mbs.length := by
    simpa only [mas,mbs,mulBits_encodeNat] using mulBits_length_le mas mbs
  have hd : ds.length ≤ das.length+dbs.length := by
    simpa only [das,dbs,mulBits_encodeNat] using mulBits_length_le das dbs
  have hi' : I ≤ P := by rw [hI]; split <;> omega
  have hil : is.length ≤ ps.length := encodeNat_length_mono hi'
  let cn := (Complexity.BitEncoding.frame mas ++ mbs).length
  let cd := (Complexity.BitEncoding.frame das ++ dbs).length
  let cc := (ratWord S is ds).length
  let W := 10*N+20
  have hcn : cn ≤ W := by dsimp [cn,W];rw [List.length_append,Complexity.BitEncoding.frame_length];omega
  have hcd : cd ≤ W := by dsimp [cd,W];rw [List.length_append,Complexity.BitEncoding.frame_length];omega
  have hcc : cc ≤ W := by
    dsimp [cc,W,ratWord]
    simp only [List.length_append,Complexity.BitEncoding.frame_length]
    omega
  have htn : rmMulTime cn ≤ rmMulTime W := by
    have hm := Nat.mul_le_mul (show 6*cn+6≤6*W+6 by omega) hcn
    dsimp [rmMulTime];omega
  have htd : rmMulTime cd ≤ rmMulTime W := by
    have hm := Nat.mul_le_mul (show 6*cd+6≤6*W+6 by omega) hcd
    dsimp [rmMulTime];omega
  have htc : rmNormTime cc ≤ rmNormTime W := by
    have hp2 := Nat.pow_le_pow_left hcc 2
    have hp3 := Nat.pow_le_pow_left hcc 3
    dsimp [rmNormTime];omega
  change (2*qa.length+2*as.length+2*bs.length+8)+((2*as.length+3)+((2*bs.length+3)+(1+
    ((2*mas.length+2*mbs.length+5)+(rmMulTime cn+((2*ps.length+2)+((8*ps.length+12)+
      ((2*das.length+2*dbs.length+5)+(rmMulTime cd+((2*ds.length+2*is.length+6)+(rmNormTime cc+1))))))))))) ≤ rmTime N
  change _ ≤ rmNormTime W+2*rmMulTime W+100*N+100
  omega

/-- Expansion of the conservative composition bound. -/
theorem rationalMultiplication_time_polynomial (N : ℕ) :
    rmTime N = 3888000*N^3+25073400*N^2+53900080*N+38623726 := by
  dsimp [rmTime,rmNormTime,rmMulTime]
  ring

/-- Canonical rational multiplication under the project's existing exact codec. -/
noncomputable def rationalMultiplicationComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.rat Complexity.BitEncoding.rat).toFinEncoding
      Complexity.BitEncoding.rat.toFinEncoding (fun p : ℚ×ℚ => p.1*p.2) where
  tm := rationalMultiplicationMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3888000*Polynomial.X^3+Polynomial.C 25073400*Polynomial.X^2+
    Polynomial.C 53900080*Polynomial.X+Polynomial.C 38623726
  outputsFun p := by
    rcases p with ⟨q,r⟩
    have go (sa sb : Bool) (a b : ℕ) (hq : q.num=signedIndex sa a) (hr : r.num=signedIndex sb b) :
        TM2OutputsInTime rationalMultiplicationMachine
          ((Complexity.BitEncoding.prod Complexity.BitEncoding.rat Complexity.BitEncoding.rat).encode (q,r))
          (some (Complexity.BitEncoding.rat.encode (q*r)))
          (let N := ((Complexity.BitEncoding.prod Complexity.BitEncoding.rat Complexity.BitEncoding.rat).encode (q,r)).length
           3888000*N^3+25073400*N^2+53900080*N+38623726) := by
      have h := rationalMultiplication_outputs sa sb a b q.den r.den
      rw [rationalMultiplication_time_polynomial] at h
      have hqword := rat_encode_signedIndex q sa a hq
      have hrword := rat_encode_signedIndex r sb b hr
      have hout : mkRat (signedIndex sa a * signedIndex sb b) (q.den*r.den)=q*r := by
        rw [← hq,← hr,Rat.mul_def']
      rw [hout] at h
      simpa [Complexity.BitEncoding.toFinEncoding,Complexity.BitEncoding.prod,hqword,hrword,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Equiv.refl,Equiv.symm] using h
    cases hq : q.num with
    | ofNat a =>
      cases hr : r.num with
      | ofNat b => simpa [Complexity.BitEncoding.toFinEncoding,Polynomial.eval_add,Polynomial.eval_mul,
          Polynomial.eval_pow,Equiv.refl,Equiv.symm] using go false false a b hq hr
      | negSucc b => simpa [Complexity.BitEncoding.toFinEncoding,Polynomial.eval_add,Polynomial.eval_mul,
          Polynomial.eval_pow,Equiv.refl,Equiv.symm] using go false true a b hq hr
    | negSucc a =>
      cases hr : r.num with
      | ofNat b => simpa [Complexity.BitEncoding.toFinEncoding,Polynomial.eval_add,Polynomial.eval_mul,
          Polynomial.eval_pow,Equiv.refl,Equiv.symm] using go true false a b hq hr
      | negSucc b => simpa [Complexity.BitEncoding.toFinEncoding,Polynomial.eval_add,Polynomial.eval_mul,
          Polynomial.eval_pow,Equiv.refl,Equiv.symm] using go true true a b hq hr

theorem fp_rational_multiplication :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.rat Complexity.BitEncoding.rat)
      Complexity.BitEncoding.rat (fun p : ℚ×ℚ => p.1*p.2) := ⟨rationalMultiplicationComputable⟩

end PlanarHom.BinaryArithmetic
