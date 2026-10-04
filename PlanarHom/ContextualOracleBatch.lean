import PlanarHom.OracleListBatch
import PlanarHom.RelationalStackTransfer

/-! A real batch-query wrapper retaining an arbitrary framed context word for
subsequent interpolation. No original input or metadata is lost across queries. -/
namespace PlanarHom.ContextualOracleBatch
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition
abbrev BStack:=PlanarHom.ListMapMachines.Stack
abbrev BLabel:=PlanarHom.ListMapMachines.Label
abbrev State:=PlanarHom.ListMapMachines.State
abbrev Stack:=Unit ⊕ BStack
inductive Phase | parse | restore | halt deriving DecidableEq,Fintype
abbrev Label:=Phase ⊕ BLabel
abbrev Statement:=Stmt (fun _ : Stack=>Bool) Label State

def store (context : Bits) (S : BStack→Bits) : Stack→Bits
  | .inl _=>context | .inr k=>S k

@[simp] theorem store_update (context : Bits) (S : BStack→Bits) (k : BStack) (xs : Bits) :
    Function.update (store context S) (.inr k) xs=store context (Function.update S k xs):=by
  funext j
  cases j with
  | inl u=>simp [store]
  | inr j=>cases j <;> cases k <;> simp [store]

@[simp] theorem store_update_context (context : Bits) (S : BStack→Bits) (xs : Bits) :
    Function.update (store context S) (.inl ()) xs=store xs S:=by
  funext j; cases j <;> simp [store]

def lift : Stmt (fun _ : BStack=>Bool) BLabel State→Statement
  | .push k f q=>.push (.inr k) f (lift q)
  | .peek k f q=>.peek (.inr k) f (lift q)
  | .pop k f q=>.pop (.inr k) f (lift q)
  | .load f q=>.load f (lift q)
  | .branch f q r=>.branch f (lift q) (lift r)
  | .goto f=>.goto (fun v=>.inr (f v))
  | .halt=>.goto (fun _=>.inl .restore)

def embedded (context : Bits) (c : PlanarHom.ListMapMachines.machine.Cfg) :
    Cfg (fun _ : Stack=>Bool) Label State:=
  ⟨(c.l.map Sum.inr).or (some (.inl .restore)),c.var,store context c.stk⟩

theorem lift_correct (context : Bits) (q : Stmt (fun _ : BStack=>Bool) BLabel State)
    (v : State) (S : BStack→Bits) :
    stepAux (lift q) v (store context S)=embedded context (stepAux q v S):=by
  induction q generalizing v S with
  | push k f q ih=>simpa only [lift,stepAux,store_update,store] using ih v (Function.update S k (f v::S k))
  | peek k f q ih=>exact ih _ _
  | pop k f q ih=>simpa only [lift,stepAux,store_update,store] using ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih=>exact ih _ _
  | branch f q r ihq ihr=>cases h:f v <;> simp only [lift,stepAux,h,Bool.cond_false,Bool.cond_true] <;> first | exact ihr _ _ | exact ihq _ _
  | goto f=>rfl
  | halt=>rfl

def resetGoto (l : Label) : Statement:=.load (fun _=>((),none)) (.goto (fun _=>l))
def program : Label→Statement
  | .inl .parse=>.pop (.inr .input) (fun v a=>(v.1,a))
      (.branch (fun v=>v.2.getD false)
        (.pop (.inr .input) (fun v a=>(v.1,a))
          (.push (.inl ()) (fun _=>true) (.push (.inl ()) (fun v=>v.2.getD false) (resetGoto (.inl .parse)))))
        (.push (.inl ()) (fun _=>false) (resetGoto (.inr .header))))
  | .inl .restore=>transferStmt (.inl ()) (.inr .input) id id (.inl .restore) (.inl .halt)
  | .inl .halt=>.halt
  | .inr l=>lift (PlanarHom.ListMapMachines.program l)

def machine : OracleTM2 where
  core:={
    tm:={K:=Stack,Γ:=fun _=>Bool,k₀:=.inr .input,k₁:=.inr .input,Λ:=Label,main:=.inl .parse,σ:=State,initialState:=((),none),Γk₀Fin:=inferInstance,m:=program}
    inputAlphabet:=Equiv.refl Bool
    outputAlphabet:=Equiv.refl Bool }
  finiteAlphabet:=fun _=>inferInstance
  queryStack:=.inr .query
  answerStack:=.inr .query
  queryAlphabet:=Equiv.refl Bool
  answerAlphabet:=Equiv.refl Bool
  request | .inr l=>(PlanarHom.ListMapMachines.machine.request l).map Sum.inr | .inl _=>none

private theorem embedded_continuation (context : Bits) (c : PlanarHom.ListMapMachines.machine.Cfg) :
    machine.continuation (embedded context c)=(PlanarHom.ListMapMachines.machine.continuation c).map Sum.inr:=by
  cases c with | mk l v S=>cases l <;> rfl

private theorem embedded_word (context : Bits) (c : PlanarHom.ListMapMachines.machine.Cfg) :
    machine.queryWord (embedded context c)=PlanarHom.ListMapMachines.machine.queryWord c:=rfl

private theorem embedded_answer (oracle : Bits→Bits) (context : Bits)
    (c : PlanarHom.ListMapMachines.machine.Cfg) (next : BLabel) :
    machine.answerCfg oracle (embedded context c) (.inr next)=
      embedded context (PlanarHom.ListMapMachines.machine.answerCfg oracle c next):=by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · exact store_update context c.stk .query _

private theorem embedded_step (context : Bits) (c d : PlanarHom.ListMapMachines.machine.Cfg)
    (h : PlanarHom.ListMapMachines.machine.core.tm.step c=some d) :
    machine.core.tm.step (embedded context c)=some (embedded context d):=by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none=>simp [FinTM2.step,step] at h
  | some l=>
    simp only [FinTM2.step,step,Option.some.injEq] at h
    subst d
    change some (stepAux (lift (PlanarHom.ListMapMachines.program l)) v (store context S))=_
    rw [lift_correct]
    rfl

/-- Embedding preserves all repeated calls and the exact transcript. -/
theorem embedded_run {oracle : Bits→Bits} (context : Bits)
    {c d : PlanarHom.ListMapMachines.machine.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (h : PlanarHom.ListMapMachines.machine.Run oracle c d steps cost qs) :
    machine.Run oracle (embedded context c) (embedded context d) steps cost qs:=by
  induction h with
  | refl c=>exact .refl _
  | ordinary hn ht hr ih=>
    apply OracleTM2.Run.ordinary _ (embedded_step context _ _ ht) ih
    rw [embedded_continuation,hn]
    rfl
  | @query c z steps cost qs next hq hr ih=>
    have hh : machine.continuation (embedded context c) = some (.inr next):=by rw [embedded_continuation,hq]; rfl
    have hrest:=ih
    rw [←embedded_answer] at hrest
    exact OracleTM2.Run.query (.inr next) hh hrest

abbrev OrdinaryRun (oracle : Bits→Bits) (c d : machine.Cfg) (n : ℕ):=
  machine.Run oracle c d n n []

def cfg (l : Label) (context : Bits) (S : BStack→Bits) : machine.Cfg:=⟨some l,((),none),store context S⟩

private theorem parse_run (oracle : Bits→Bits) (word tail context : Bits) :
    OrdinaryRun oracle (cfg (.inl .parse) context (pointStack .input (BitEncoding.frame word++tail)))
      (embedded ((BitEncoding.frame word).reverse++context) (PlanarHom.ListMapMachines.machine.initial tail))
      (word.length+1):=by
  induction word generalizing context with
  | nil=>
    apply OracleTM2.Run.ordinary rfl _ (.refl _)
    apply congrArg some
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · simp [machine,program,stepAux,resetGoto,embedded,store,BitEncoding.frame,OracleTM2.initial,initList,pointStack,Equiv.refl]
      funext k
      cases k with
      | inl u=>cases u; rfl
      | inr k=>cases k <;> simp [store,PlanarHom.ListMapMachines.machine,Equiv.refl]
  | cons b word ih=>
    have hs : machine.core.tm.step (cfg (.inl .parse) context (pointStack .input (BitEncoding.frame (b::word)++tail)))=
        some (cfg (.inl .parse) (b::true::context) (pointStack .input (BitEncoding.frame word++tail))):=by
      simp [machine,FinTM2.step,step,program,stepAux,resetGoto,cfg,store,BitEncoding.frame,pointStack]
    have h:=OracleTM2.Run.ordinary (m:=machine) (oracle:=oracle) rfl hs (ih (b::true::context))
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc] using h

private theorem ordinary_trans (oracle : Bits→Bits) {c d e : machine.Cfg} {n k : ℕ}
    (h : OrdinaryRun oracle c d n) (h' : OrdinaryRun oracle d e k) : OrdinaryRun oracle c e (n+k):=by
  simpa only [List.nil_append] using h.trans h'

private theorem restore_run (oracle : Bits→Bits) (context output : Bits) :
    OrdinaryRun oracle (embedded context (PlanarHom.ListMapMachines.machine.final output))
      (machine.final (context.reverse++output)) (context.length+2):=by
  have ht:=transfer_rel (OrdinaryRun oracle) (@ordinary_trans oracle) (Sum.inl ()) (Sum.inr PlanarHom.ListMapMachines.Stack.input)
    (by simp) id id (Sum.inl Phase.restore) (Sum.inl Phase.halt)
    (fun v r S=>OracleTM2.Run.ordinary (m:=machine) (oracle:=oracle) rfl rfl (.refl _))
    () none (store context (pointStack .input output))
  have hs : transferStore (Sum.inl ()) (Sum.inr PlanarHom.ListMapMachines.Stack.input) (id : Bool→Bool)
      (store context (pointStack .input output))=store [] (pointStack .input (context.reverse++output)):=by
    funext k; cases k with
    | inl u=>cases u; simp [transferStore,store]
    | inr k=>cases k <;> simp [transferStore,store,pointStack]
  simp only [Function.id_comp,hs] at ht
  have hh : OrdinaryRun oracle (cfg (.inl .halt) [] (pointStack .input (context.reverse++output)))
      (machine.final (context.reverse++output)) 1:=by
    apply OracleTM2.Run.ordinary rfl _ (.refl _)
    apply congrArg some
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k; cases k with
      | inl u=>cases u; rfl
      | inr k=>cases k <;> simp [machine,program,stepAux,OracleTM2.final,haltList,store,pointStack,Equiv.refl]
  have h:=ordinary_trans oracle ht hh
  have he : embedded context (PlanarHom.ListMapMachines.machine.final output)=
      cfg (.inl .restore) context (pointStack .input output):=by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k
      cases k with
      | inl u=>rfl
      | inr k=>cases k <;> simp [embedded,OracleTM2.final,haltList,PlanarHom.ListMapMachines.machine,
          Equiv.refl,pointStack,cfg,store]
  rw [he]
  simpa only [cfg,store,Nat.add_assoc] using h

/-- Whole wrapper: save the exact context frame, run every query, then restore
that frame onto the complete serialized answer list. -/
theorem run {oracle : Bits→Bits} (context input output : Bits) {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (h : PlanarHom.ListMapMachines.machine.Run oracle (PlanarHom.ListMapMachines.machine.initial input)
      (PlanarHom.ListMapMachines.machine.final output) steps cost qs) :
    machine.Run oracle (machine.initial (BitEncoding.frame context++input))
      (machine.final (BitEncoding.frame context++output))
      ((context.length+1)+steps+((BitEncoding.frame context).length+2))
      ((context.length+1)+cost+((BitEncoding.frame context).length+2)) qs:=by
  have hp:=parse_run oracle context input []
  simp only [List.append_nil] at hp
  have hm:=embedded_run (BitEncoding.frame context).reverse h
  have hr:=restore_run oracle (BitEncoding.frame context).reverse output
  simp only [List.length_reverse,List.reverse_reverse] at hr
  have hall:=(hp.trans hm).trans hr
  have hi : machine.initial (BitEncoding.frame context++input)=
      cfg (.inl .parse) [] (pointStack .input (BitEncoding.frame context++input)):=by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k
      cases k with
      | inl u=>cases u; rfl
      | inr k=>cases k <;> simp [machine,OracleTM2.initial,initList,cfg,store,pointStack,Equiv.refl]
  rw [hi]
  simpa only [List.nil_append,List.append_nil] using hall

end PlanarHom.ContextualOracleBatch
