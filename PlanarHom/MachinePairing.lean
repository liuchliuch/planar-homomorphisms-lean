import PlanarHom.OracleSubstitution
import PlanarHom.PairProjectionMachines

/-! Actual TM2 pairing of two computed results from one preserved input. -/

namespace PlanarHom.MachinePairing
noncomputable section
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition
open PlanarHom.OracleSubstitution hiding machine program cfg_ext

inductive Phase | save | copy | frame | restore | halt deriving DecidableEq, Fintype
abbrev Labels (a b : FinTM2) := Phase ⊕ (a.Λ ⊕ b.Λ)
def leftLabel {a b : FinTM2} (l : a.Λ) : Labels a b := .inr (.inl l)
def rightLabel {a b : FinTM2} (l : b.Λ) : Labels a b := .inr (.inr l)
def phase {a b : FinTM2} (p : Phase) : Labels a b := .inl p

def leftStmt (a b : FinTM2) (q : a.Stmt) : Stmt (Alphabet a b) (Labels a b) (State a b) :=
  redirectHalt (rightLabel b.main)
    (renameState (callerState a b) (liftStmt (callerEmbedding a b) leftLabel q))

def rightStmt (a b : FinTM2) (q : b.Stmt) : Stmt (Alphabet a b) (Labels a b) (State a b) :=
  redirectHalt (phase .frame)
    (renameState (calleeState a b) (liftStmt (calleeEmbedding a b) rightLabel q))

def program (a b : TM2ComputableAux Bool Bool) : Labels a.tm b.tm →
    Stmt (Alphabet a.tm b.tm) (Labels a.tm b.tm) (State a.tm b.tm)
  | .inl .save => transferStmt (.inr (.inl b.tm.k₀)) temp b.inputAlphabet id (phase .save) (phase .copy)
  | .inl .copy => transfer₂Stmt temp (.inr (.inl b.tm.k₀)) (.inl a.tm.k₀) id b.inputAlphabet.symm a.inputAlphabet.symm
      (phase .copy) (leftLabel a.tm.main)
  | .inl .frame => .pop (.inl a.tm.k₁) (fun v x=>(v.1,x.map a.outputAlphabet))
      (.branch (fun v=>v.2.isSome)
        (.push temp (fun _=>true) (.push temp (fun v=>v.2.getD false)
          (.load (fun v=>(v.1,none)) (.goto (fun _=>phase .frame)))))
        (.push temp (fun _=>false) (.load (fun v=>(v.1,none)) (.goto (fun _=>phase .restore)))))
  | .inl .restore => transferStmt temp (.inr (.inl b.tm.k₁)) id b.outputAlphabet.symm (phase .restore) (phase .halt)
  | .inl .halt => .halt
  | .inr (.inl l) => leftStmt a.tm b.tm (a.tm.m l)
  | .inr (.inr l) => rightStmt a.tm b.tm (b.tm.m l)

def machine (a b : TM2ComputableAux Bool Bool) : FinTM2 := by
  letI:=a.tm.kFin; letI:=b.tm.kFin; letI:=a.tm.ΛFin; letI:=b.tm.ΛFin
  letI:=a.tm.σFin; letI:=b.tm.σFin
  exact { K:=Bank a.tm b.tm, Γ:=Alphabet a.tm b.tm, k₀:=.inr (.inl b.tm.k₀), k₁:=.inr (.inl b.tm.k₁), Λ:=Labels a.tm b.tm, main:=phase .save, σ:=State a.tm b.tm, initialState:=((a.tm.initialState,b.tm.initialState),none), Γk₀Fin:=b.tm.Γk₀Fin, m:=program a b }

def leftCfg (a b : FinTM2) (B : ∀ k,List (b.Γ k)) (c : a.Cfg) :
    Cfg (Alphabet a b) (Labels a b) (State a b) :=
  ⟨(c.l.map leftLabel).or (some (rightLabel b.main)),((c.var,b.initialState),none),store a b c.stk B []⟩

def rightCfg (a b : FinTM2) (A : ∀ k,List (a.Γ k)) (c : b.Cfg) :
    Cfg (Alphabet a b) (Labels a b) (State a b) :=
  ⟨(c.l.map rightLabel).or (some (phase .frame)),((a.initialState,c.var),none),store a b A c.stk []⟩

theorem leftStmt_correct (a b : FinTM2) (q : a.Stmt) (v : a.σ)
    (A : ∀ k,List (a.Γ k)) (B : ∀ k,List (b.Γ k)) :
    stepAux (leftStmt a b q) ((v,b.initialState),none) (store a b A B []) =
      leftCfg a b B (stepAux q v A) := by
  let e:=callerEmbedding a b
  have hs : e.Represents A (store a b A B []) := by intro k; change A k=(A k).map id; simp
  have h:=liftStmt_correct e (leftLabel (a:=a) (b:=b)) q v (b.initialState,(none : Option Bool)) A (store a b A B []) hs
  unfold leftStmt
  rw [redirectHalt_correct]
  change continueCfg _ (stepAux (renameState (callerState a b) (liftStmt e leftLabel q))
    ((callerState a b) (v,(b.initialState,none))) _) = _
  rw [renameState_correct]
  apply OracleSubstitution.cfg_ext
  · exact congrArg (fun l=>l.or (some (rightLabel b.main))) h.1
  · exact congrArg (callerState a b) h.2.1
  · funext k
    cases k with
    | inl k =>
      have hh:=h.2.2 k
      change _=List.map id _ at hh
      simpa only [List.map_id] using hh
    | inr k =>
      have ht := liftStmt_untouched e (leftLabel (a:=a) (b:=b)) q (v,(b.initialState,(none : Option Bool))) (store a b A B []) (.inr k)
        (by intro j; simp [e,callerEmbedding])
      cases k <;> exact ht

theorem rightStmt_correct (a b : FinTM2) (q : b.Stmt) (v : b.σ)
    (A : ∀ k,List (a.Γ k)) (B : ∀ k,List (b.Γ k)) :
    stepAux (rightStmt a b q) ((a.initialState,v),none) (store a b A B []) =
      rightCfg a b A (stepAux q v B) := by
  let e:=calleeEmbedding a b
  have hs : e.Represents B (store a b A B []) := by intro k; change B k=(B k).map id; simp
  have h:=liftStmt_correct e (rightLabel (a:=a) (b:=b)) q v (a.initialState,(none : Option Bool)) B (store a b A B []) hs
  unfold rightStmt
  rw [redirectHalt_correct]
  change continueCfg _ (stepAux (renameState (calleeState a b) (liftStmt e rightLabel q))
    ((calleeState a b) (v,(a.initialState,none))) _) = _
  rw [renameState_correct]
  apply OracleSubstitution.cfg_ext
  · exact congrArg (fun l=>l.or (some (phase .frame))) h.1
  · exact congrArg (calleeState a b) h.2.1
  · funext k
    cases k with
    | inl k =>
      exact liftStmt_untouched e rightLabel q (v,(a.initialState,none)) _ (.inl k)
        (by intro j; simp [e,calleeEmbedding])
    | inr k => cases k with
      | inl k =>
        have hh:=h.2.2 k
        change _=List.map id _ at hh
        simpa only [List.map_id] using hh
      | inr u =>
        exact liftStmt_untouched e rightLabel q (v,(a.initialState,none)) _ (.inr (.inr u))
          (by intro j; simp [e,calleeEmbedding])

variable (a b : TM2ComputableAux Bool Bool)

theorem left_step (B : ∀ k,List (b.tm.Γ k)) (c d : a.tm.Cfg) (hs : a.tm.step c=some d) :
    (machine a b).step (leftCfg a.tm b.tm B c)=some (leftCfg a.tm b.tm B d) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [FinTM2.step,step] at hs
  | some l =>
    simp only [FinTM2.step,step,Option.some.injEq] at hs
    subst d
    change some (stepAux (leftStmt a.tm b.tm (a.tm.m l)) _ _)=_
    rw [leftStmt_correct]

theorem right_step (A : ∀ k,List (a.tm.Γ k)) (c d : b.tm.Cfg) (hs : b.tm.step c=some d) :
    (machine a b).step (rightCfg a.tm b.tm A c)=some (rightCfg a.tm b.tm A d) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [FinTM2.step,step] at hs
  | some l =>
    simp only [FinTM2.step,step,Option.some.injEq] at hs
    subst d
    change some (stepAux (rightStmt a.tm b.tm (b.tm.m l)) _ _)=_
    rw [rightStmt_correct]

theorem left_run (B : ∀ k,List (b.tm.Γ k)) (c d : a.tm.Cfg) (n : ℕ)
    (hs : (fun c : Option a.tm.Cfg=>c.bind a.tm.step)^[n] (some c)=some d) :
    (fun c : Option (machine a b).Cfg=>c.bind (machine a b).step)^[n]
      (some (leftCfg a.tm b.tm B c))=some (leftCfg a.tm b.tm B d) := by
  obtain ⟨e,he,hr⟩:=simulate_iterations a.tm.step (machine a b).step
    (fun c d=>d=leftCfg a.tm b.tm B c)
    (by intro c d e hs he; subst e; exact ⟨_,left_step a b B c d hs,rfl⟩)
    c d (leftCfg a.tm b.tm B c) n hs rfl
  simpa [hr] using he

theorem right_run (A : ∀ k,List (a.tm.Γ k)) (c d : b.tm.Cfg) (n : ℕ)
    (hs : (fun c : Option b.tm.Cfg=>c.bind b.tm.step)^[n] (some c)=some d) :
    (fun c : Option (machine a b).Cfg=>c.bind (machine a b).step)^[n]
      (some (rightCfg a.tm b.tm A c))=some (rightCfg a.tm b.tm A d) := by
  obtain ⟨e,he,hr⟩:=simulate_iterations b.tm.step (machine a b).step
    (fun c d=>d=rightCfg a.tm b.tm A c)
    (by intro c d e hs he; subst e; exact ⟨_,right_step a b A c d hs,rfl⟩)
    c d (rightCfg a.tm b.tm A c) n hs rfl
  simpa [hr] using he

def stage (p : Phase) (A : ∀ k,List (a.tm.Γ k)) (B : ∀ k,List (b.tm.Γ k)) (T : Bits) :
    (machine a b).Cfg := ⟨some (phase p),((a.tm.initialState,b.tm.initialState),none),store a.tm b.tm A B T⟩

abbrev iter (n : ℕ) (c : (machine a b).Cfg) : Option (machine a b).Cfg :=
  (fun c : Option (machine a b).Cfg=>c.bind (machine a b).step)^[n] (some c)

theorem iter_trans {c d e : (machine a b).Cfg} {n m : ℕ}
    (h : iter a b n c=some d) (h' : iter a b m d=some e) : iter a b (m+n) c=some e := by
  unfold iter at *
  rw [Function.iterate_add_apply,h]
  exact h'

theorem initial_eq (x : Bits) : initList (machine a b) (x.map b.inputAlphabet.symm) =
    stage a b .save (fun _=>[]) (pointStack b.tm.k₀ (x.map b.inputAlphabet.symm)) [] := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · rw [initList_stk]
    change pointStack (.inr (.inl b.tm.k₀)) _ = store a.tm b.tm _ (pointStack b.tm.k₀ _) []
    simp only [pointStack,←store_update_right,store_empty]

theorem empty_temp_store (A B : FinTM2) (T : Bits) :
    Function.update (fun k : Bank A B=>([] : List (Alphabet A B k))) temp T = store A B (fun _=>[]) (fun _=>[]) T := by
  have h:=store_update_temp A B (fun _=>[]) (fun _=>[]) [] T
  simpa only [store_empty] using h

theorem save_run (x : Bits) :
    iter a b (x.length+1) (stage a b .save (fun _=>[]) (pointStack b.tm.k₀ (x.map b.inputAlphabet.symm)) []) =
      some (stage a b .copy (fun _=>[]) (fun _=>[]) x.reverse) := by
  have h:=transfer_run (program a b) (.inr (.inl b.tm.k₀)) temp (by intro h; cases h)
    b.inputAlphabet id (phase .save) (phase .copy) rfl (a.tm.initialState,b.tm.initialState) none
    (store a.tm b.tm (fun _=>[]) (pointStack b.tm.k₀ (x.map b.inputAlphabet.symm)) [])
  simpa [iter,stage,machine,FinTM2.step,transferStore,store_update_right,store_update_temp,
    pointStack,Function.comp_def,List.map_map,Function.update_eq_self,empty_temp_store] using h

theorem copy_run (x : Bits) :
    iter a b (x.length+1) (stage a b .copy (fun _=>[]) (fun _=>[]) x.reverse) =
      some (leftCfg a.tm b.tm (pointStack b.tm.k₀ (x.map b.inputAlphabet.symm))
        (initList a.tm (x.map a.inputAlphabet.symm))) := by
  have h:=transfer₂_run (program a b) temp (.inr (.inl b.tm.k₀)) (.inl a.tm.k₀)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    id b.inputAlphabet.symm a.inputAlphabet.symm (phase .copy) (leftLabel a.tm.main) rfl
    (a.tm.initialState,b.tm.initialState) none (store a.tm b.tm (fun _=>[]) (fun _=>[]) x.reverse)
  simpa [iter,stage,machine,FinTM2.step,transfer₂Store,transferStore,store_update_temp,
    store_update_right,store_update_left,pointStack,Function.comp_def,List.map_reverse,
    leftCfg,initList_stk] using h

theorem left_handoff (x y : Bits) :
    leftCfg a.tm b.tm (pointStack b.tm.k₀ (x.map b.inputAlphabet.symm))
      (haltList a.tm (y.map a.outputAlphabet.symm)) =
    rightCfg a.tm b.tm (pointStack a.tm.k₁ (y.map a.outputAlphabet.symm))
      (initList b.tm (x.map b.inputAlphabet.symm)) := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · simp only [leftCfg,rightCfg,initList_stk,haltList_stk]

theorem right_handoff (y z : Bits) :
    rightCfg a.tm b.tm (pointStack a.tm.k₁ (y.map a.outputAlphabet.symm))
      (haltList b.tm (z.map b.outputAlphabet.symm)) =
    stage a b .frame (pointStack a.tm.k₁ (y.map a.outputAlphabet.symm))
      (pointStack b.tm.k₁ (z.map b.outputAlphabet.symm)) [] := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · simp only [rightCfg,stage,haltList_stk]

theorem frame_step_nil (B : ∀ k,List (b.tm.Γ k)) (T : Bits) :
    (machine a b).step (stage a b .frame (pointStack a.tm.k₁ []) B T) =
      some (stage a b .restore (fun _=>[]) B (false::T)) := by
  simp [machine,FinTM2.step,step,program,phase,stage,pointStack,stepAux,
    store_update_left,store_update_temp,Function.update_eq_self]

theorem frame_step_cons (y : a.tm.Γ a.tm.k₁) (ys : List (a.tm.Γ a.tm.k₁))
    (B : ∀ k,List (b.tm.Γ k)) (T : Bits) :
    (machine a b).step (stage a b .frame (pointStack a.tm.k₁ (y::ys)) B T) =
      some (stage a b .frame (pointStack a.tm.k₁ ys) B (a.outputAlphabet y::true::T)) := by
  simp [machine,FinTM2.step,step,program,phase,stage,pointStack,stepAux,
    store_update_left,store_update_temp]

theorem frame_run (ys : List (a.tm.Γ a.tm.k₁)) (B : ∀ k,List (b.tm.Γ k)) (T : Bits) :
    iter a b (ys.length+1) (stage a b .frame (pointStack a.tm.k₁ ys) B T) =
      some (stage a b .restore (fun _=>[]) B ((BitEncoding.frame (ys.map a.outputAlphabet)).reverse++T)) := by
  induction ys generalizing T with
  | nil => simpa [iter,BitEncoding.frame] using frame_step_nil a b B T
  | cons y ys ih =>
    change (fun c : Option (machine a b).Cfg=>c.bind (machine a b).step)^[ys.length+1+1]
      (some (stage a b .frame (pointStack a.tm.k₁ (y::ys)) B T)) = _
    rw [Function.iterate_succ_apply]
    change (fun c : Option (machine a b).Cfg=>c.bind (machine a b).step)^[ys.length+1]
      ((machine a b).step (stage a b .frame (pointStack a.tm.k₁ (y::ys)) B T)) = _
    rw [frame_step_cons]
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc] using ih (a.outputAlphabet y::true::T)

theorem restore_run (y z : Bits) :
    iter a b ((BitEncoding.frame y).length+1)
      (stage a b .restore (fun _=>[]) (pointStack b.tm.k₁ (z.map b.outputAlphabet.symm)) (BitEncoding.frame y).reverse) =
      some (stage a b .halt (fun _=>[]) (pointStack b.tm.k₁ ((BitEncoding.frame y++z).map b.outputAlphabet.symm)) []) := by
  have h:=transfer_run (program a b) temp (.inr (.inl b.tm.k₁)) (by intro h; cases h)
    id b.outputAlphabet.symm (phase .restore) (phase .halt) rfl
    (a.tm.initialState,b.tm.initialState) none
    (store a.tm b.tm (fun _=>[]) (pointStack b.tm.k₁ (z.map b.outputAlphabet.symm)) (BitEncoding.frame y).reverse)
  simpa [-BitEncoding.frame_length,iter,stage,machine,FinTM2.step,transferStore,store_update_temp,store_update_right,
    pointStack,Function.comp_def,List.map_reverse,List.map_append] using h

theorem halt_run (z : Bits) :
    iter a b 1 (stage a b .halt (fun _=>[]) (pointStack b.tm.k₁ (z.map b.outputAlphabet.symm)) []) =
      some (haltList (machine a b) (z.map b.outputAlphabet.symm)) := by
  change some (Turing.TM2.stepAux .halt _ _) = _
  apply congrArg some
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · rw [haltList_stk]
    change store a.tm b.tm (fun _=>[]) (pointStack b.tm.k₁ _) [] = pointStack (.inr (.inl b.tm.k₁)) _
    simp only [pointStack,←store_update_right,store_empty]

/-- Exact paired output after input preservation, both actual computations,
and materialized framing/copying of the first output. -/
def pairing_outputs (x y z : Bits) (n m : ℕ)
    (ha : TM2OutputsInTime a.tm (x.map a.inputAlphabet.symm) (some (y.map a.outputAlphabet.symm)) n)
    (hb : TM2OutputsInTime b.tm (x.map b.inputAlphabet.symm) (some (z.map b.outputAlphabet.symm)) m) :
    TM2OutputsInTime (machine a b) (x.map b.inputAlphabet.symm)
      (some ((BitEncoding.frame y++z).map b.outputAlphabet.symm)) (n+m+2*x.length+3*y.length+6) where
  steps := ha.steps+hb.steps+2*x.length+3*y.length+6
  steps_le_m := by have h₁:=ha.steps_le_m; have h₂:=hb.steps_le_m; omega
  evals_in_steps := by
    have h₁:=iter_trans a b (save_run a b x) (copy_run a b x)
    have h₂:=left_run a b (pointStack b.tm.k₀ (x.map b.inputAlphabet.symm))
      _ _ ha.steps ha.evals_in_steps
    rw [left_handoff] at h₂
    have h₃:=right_run a b (pointStack a.tm.k₁ (y.map a.outputAlphabet.symm))
      _ _ hb.steps hb.evals_in_steps
    rw [right_handoff] at h₃
    have h₄:=frame_run a b (y.map a.outputAlphabet.symm) (pointStack b.tm.k₁ (z.map b.outputAlphabet.symm)) []
    simp only [List.length_map,List.map_map,Function.comp_def,Equiv.apply_symm_apply,List.map_id_fun',List.append_nil] at h₄
    have h₅:=restore_run a b y z
    have h₆:=halt_run a b (BitEncoding.frame y++z)
    have hh:=iter_trans a b (iter_trans a b (iter_trans a b (iter_trans a b (iter_trans a b h₁ h₂) h₃) h₄) h₅) h₆
    rw [initial_eq]
    convert hh using 1
    simp only [BitEncoding.frame_length]
    congr 1
    omega

/-- Construct a real TM2 computer for a pair of independently computed results.
The same input is explicitly copied; neither result is recomputed from the other. -/
def pairComputers {α β γ : Type} {ea : BitEncoding α} {eb : BitEncoding β} {ec : BitEncoding γ}
    {f : α→β} {g : α→γ}
    (hf : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f)
    (hg : TM2ComputableInPolyTime ea.toFinEncoding ec.toFinEncoding g) :
    TM2ComputableInPolyTime ea.toFinEncoding (eb.prod ec).toFinEncoding (fun x=>(f x,g x)) := by
  refine {
    tm:=machine hf.toTM2ComputableAux hg.toTM2ComputableAux
    inputAlphabet:=hg.inputAlphabet
    outputAlphabet:=hg.outputAlphabet
    time:=hf.time+hg.time+Polynomial.C 2*Polynomial.X+
      Polynomial.C 3*outputLengthPolynomial hf+Polynomial.C 6
    outputsFun:=?_ }
  intro x
  have h:=pairing_outputs hf.toTM2ComputableAux hg.toTM2ComputableAux
    (ea.encode x) (eb.encode (f x)) (ec.encode (g x)) _ _ (hf.outputsFun x) (hg.outputsFun x)
  refine {steps:=h.steps,evals_in_steps:=h.evals_in_steps,steps_le_m:=?_}
  apply h.steps_le_m.trans
  have hy:=encoded_output_length_le hf x
  simp only [BitEncoding.toFinEncoding,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at *
  omega

/-- Map the two independently encoded components with actual pairing and
projection compilers. This is useful for assembling exact arithmetic operands. -/
def productMapComputers {α β γ δ : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {ec : BitEncoding γ} {ed : BitEncoding δ} {f : α→β} {g : γ→δ}
    (hf : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f)
    (hg : TM2ComputableInPolyTime ec.toFinEncoding ed.toFinEncoding g) :
    TM2ComputableInPolyTime (ea.prod ec).toFinEncoding (eb.prod ed).toFinEncoding (Prod.map f g) :=
  pairComputers (composeComputers (PairProjectionMachines.fstEncodingComputer ea ec) hf)
    (composeComputers (PairProjectionMachines.sndEncodingComputer ea ec) hg)

end
end PlanarHom.MachinePairing

namespace PlanarHom.Complexity

theorem FP.pair {α β γ : Type} {ea : BitEncoding α} {eb : BitEncoding β} {ec : BitEncoding γ}
    {f : α→β} {g : α→γ} (hf : FP ea eb f) (hg : FP ea ec g) :
    FP ea (eb.prod ec) (fun x=>(f x,g x)) := by
  obtain ⟨f⟩:=hf; obtain ⟨g⟩:=hg
  exact ⟨MachinePairing.pairComputers f g⟩

theorem FP.prodMap {α β γ δ : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {ec : BitEncoding γ} {ed : BitEncoding δ} {f : α→β} {g : γ→δ}
    (hf : FP ea eb f) (hg : FP ec ed g) : FP (ea.prod ec) (eb.prod ed) (Prod.map f g) := by
  obtain ⟨f⟩:=hf; obtain ⟨g⟩:=hg
  exact ⟨MachinePairing.productMapComputers f g⟩

end PlanarHom.Complexity
