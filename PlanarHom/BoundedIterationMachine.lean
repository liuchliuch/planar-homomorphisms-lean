import PlanarHom.OracleSubstitutionOnTrace
import PlanarHom.OracleReductionComposition
import PlanarHom.InputLengthMachine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual finite-control iteration of typed polynomial-time machines, with an
explicit bound on every intermediate codeword. Off-code behavior is irrelevant:
all substituted calls are proved to lie on the canonical query transcript. -/
namespace PlanarHom.BoundedIterationMachine
open Turing Turing.TM2 Polynomial PlanarHom.Complexity PlanarHom.MachineComposition

inductive Stack | input | count deriving DecidableEq, Fintype
inductive Label | parse | check | query deriving DecidableEq, Fintype
abbrev State:=Unit × Option Bool
abbrev Statement:=Stmt (fun _ : Stack=>Bool) Label State

def store (xs count : Bits) : Stack→Bits | .input=>xs | .count=>count

def resetGoto (l : Label) : Statement:=.load (fun _=>((),none)) (.goto (fun _=>l))
def program : Label→Statement
  | .parse=>.pop .input (fun v a=>(v.1,a))
      (.branch (fun v=>v.2.getD false)
        (.pop .input (fun v a=>(v.1,a)) (.push .count (fun _=>true) (resetGoto .parse)))
        (resetGoto .check))
  | .check=>.pop .count (fun v a=>(v.1,a))
      (.branch (fun v=>v.2.isSome) (resetGoto .query) (.load (fun _=>((),none)) .halt))
  | .query=>.halt

def machine : OracleTM2 where
  core := {
    tm := {
      K:=Stack
      Γ:=fun _=>Bool
      k₀:=.input
      k₁:=.input
      Λ:=Label
      main:=.parse
      σ:=State
      initialState:=((),none)
      Γk₀Fin:=inferInstance
      m:=program }
    inputAlphabet:=Equiv.refl Bool
    outputAlphabet:=Equiv.refl Bool }
  finiteAlphabet:=fun _=>inferInstance
  queryStack:=.input
  answerStack:=.input
  queryAlphabet:=Equiv.refl Bool
  answerAlphabet:=Equiv.refl Bool
  request | .query=>some .check | _=>none

def cfg (l : Label) (xs count : Bits) : machine.Cfg:=⟨some l,((),none),store xs count⟩

def typedOracle {α : Type} (e : BitEncoding α) (f : α→α) (q : Bits) : Bits:=
  match e.decode q with | none=>[] | some a=>e.encode (f a)
@[simp] theorem typedOracle_encode {α : Type} (e : BitEncoding α) (f : α→α) (a : α) :
    typedOracle e f (e.encode a)=e.encode (f a):=by simp [typedOracle,e.decode_encode]

def Good {α : Type} (e : BitEncoding α) (f : α→α) (qa : Bits × Bits) : Prop:=
  ∃a,qa=(e.encode a,e.encode (f a))

def Runs {α : Type} (e : BitEncoding α) (f : α→α) (c d : machine.Cfg) (bound : ℕ) : Prop:=
  ∃s t qs,machine.Run (typedOracle e f) c d s t qs ∧ t≤bound ∧ ∀qa∈qs,Good e f qa

variable {α : Type} {e : BitEncoding α} {f : α→α}
theorem Runs.trans {c d z : machine.Cfg} {n k : ℕ} (h : Runs e f c d n) (h' : Runs e f d z k) :
    Runs e f c z (n+k):=by
  obtain ⟨s,t,qs,hr,ht,hgood⟩:=h
  obtain ⟨s',t',qs',hr',ht',hgood'⟩:=h'
  refine ⟨_,_,_,hr.trans hr',Nat.add_le_add ht ht',?_⟩
  intro qa ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hgood qa ha
  · exact hgood' qa ha

theorem Runs.mono {c d : machine.Cfg} {n k : ℕ} (h : Runs e f c d n) (hk : n≤k) : Runs e f c d k:=by
  obtain ⟨s,t,qs,hr,ht,hgood⟩:=h
  exact ⟨s,t,qs,hr,ht.trans hk,hgood⟩

theorem ordinary {c d : machine.Cfg} (hn : machine.continuation c=none)
    (hs : machine.core.tm.step c=some d) : Runs e f c d 1:=
  ⟨1,1,[],.ordinary hn hs (.refl d),by rfl,by simp⟩

private theorem parse_cons (b : Bool) (tail count : Bits) :
    Runs e f (cfg .parse (true::b::tail) count) (cfg .parse tail (true::count)) 1:=by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,resetGoto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem parse_nil (tail count : Bits) :
    Runs e f (cfg .parse (false::tail) count) (cfg .check tail count) 1:=by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,resetGoto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem unary_append_true (n : ℕ) (xs : Bits) :
    Computability.unaryEncodeNat n++true::xs=Computability.unaryEncodeNat (n+1)++xs:=by
  induction n with
  | zero=>rfl
  | succ n ih=>simpa only [Computability.unaryEncodeNat,List.cons_append] using congrArg (List.cons true) ih

theorem parse_run (F tail count : Bits) :
    Runs e f (cfg .parse (BitEncoding.frame F++tail) count)
      (cfg .check tail (Computability.unaryEncodeNat F.length++count)) (F.length+1):=by
  induction F generalizing count with
  | nil=>simpa [BitEncoding.frame,Computability.unaryEncodeNat] using (parse_nil (e:=e) (f:=f) tail count)
  | cons b F ih=>
    have h:=(parse_cons (e:=e) (f:=f) b (BitEncoding.frame F++tail) count).trans (ih (true::count))
    simpa only [BitEncoding.frame,List.cons_append,List.length_cons,unary_append_true,Nat.add_comm] using h

private theorem check_more (xs count : Bits) :
    Runs e f (cfg .check xs (true::count)) (cfg .query xs count) 1:=by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,resetGoto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem finish (xs : Bits) : Runs e f (cfg .check xs []) (machine.final xs) 1:=by
  apply ordinary rfl
  apply congrArg some
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> simp [machine,program,stepAux,store,OracleTM2.final,haltList,Equiv.refl]

theorem query_run (a : α) (count : Bits) :
    Runs e f (cfg .query (e.encode a) count) (cfg .check (e.encode (f a)) count)
      (1+(e.encode a).length+(e.encode (f a)).length):=by
  have hq : machine.continuation (cfg .query (e.encode a) count)=some .check:=rfl
  have hw : machine.queryWord (cfg .query (e.encode a) count)=e.encode a:=by
    simp [machine,OracleTM2.queryWord,cfg,store,Equiv.refl]
  have he : machine.answerCfg (typedOracle e f) (cfg .query (e.encode a) count) .check=
      cfg .check (e.encode (f a)) count:=by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · simp [OracleTM2.answerCfg,machine,OracleTM2.queryWord,cfg,Equiv.refl,store]
      funext k; cases k <;> rfl
  refine ⟨1,_,[(e.encode a,e.encode (f a))],?_,Nat.le_refl _,?_⟩
  · have h:=OracleTM2.Run.query (m:=machine) (oracle:=typedOracle e f) Label.check hq
      (OracleTM2.Run.refl (machine.answerCfg (typedOracle e f) (cfg .query (e.encode a) count) .check))
    simpa only [he,hw,Nat.zero_add,typedOracle_encode] using h
  · intro qa ha
    have hqa:=List.mem_singleton.mp ha
    exact ⟨a,hqa⟩

/-- Iteration count is unary and the live data size is bounded explicitly at
every intermediate state, not merely at the final result. -/
theorem loop_run (n : ℕ) (a : α) (L : ℕ)
    (hL : ∀i,i≤n→(e.encode (f^[i] a)).length≤L) :
    Runs e f (cfg .check (e.encode a) (Computability.unaryEncodeNat n))
      (machine.final (e.encode (f^[n] a))) (n*(2*L+2)+1):=by
  induction n generalizing a with
  | zero=>simpa [Computability.unaryEncodeNat] using (finish (e:=e) (f:=f) (e.encode a))
  | succ n ih=>
    have ha : (e.encode a).length≤L:=hL 0 (by omega)
    have hf : (e.encode (f a)).length≤L:=hL 1 (by omega)
    have hq:=(query_run (e:=e) (f:=f) a (Computability.unaryEncodeNat n)).mono
      (show 1+(e.encode a).length+(e.encode (f a)).length≤2*L+1 by omega)
    have hi:=ih (f a) (fun i hi=>by
      simpa [Function.iterate_succ_apply] using hL (i+1) (by omega))
    have h:=((check_more (e:=e) (f:=f) (e.encode a) (Computability.unaryEncodeNat n)).trans hq).trans hi
    change Runs e f (cfg .check (e.encode a) (true::Computability.unaryEncodeNat n))
      (machine.final (e.encode (f^[n] (f a)))) ((n+1)*(2*L+2)+1)
    convert h using 1
    ring


/-- Exact complete oracle execution. The returned trace only contains canonical
inputs and their canonical typed outputs. -/
theorem run (n : ℕ) (a : α) (L : ℕ)
    (hL : ∀i,i≤n→(e.encode (f^[i] a)).length≤L) :
    Runs e f (machine.initial ((BitEncoding.unaryNat.prod e).encode (n,a)))
      (machine.final (e.encode (f^[n] a))) (n*(2*L+3)+2):=by
  have hp:=parse_run (e:=e) (f:=f) (BitEncoding.unaryNat.encode n) (e.encode a) []
  simp only [BitEncoding.unaryNat_length,List.append_nil] at hp
  have h:=hp.trans (loop_run n a L hL)
  have hi : machine.initial ((BitEncoding.unaryNat.prod e).encode (n,a))=
      cfg .parse (BitEncoding.frame (BitEncoding.unaryNat.encode n)++e.encode a) []:=by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k; cases k <;> simp [machine,OracleTM2.initial,initList,cfg,store,BitEncoding.prod,Equiv.refl]
  rw [hi]
  convert h using 1
  ring

/-- The actual compiler for polynomially bounded iteration of a typed FP
function. The polynomial size invariant is a mathematical bound, not an
unimplemented execution or arithmetic primitive. -/
noncomputable def computer (e : BitEncoding α) (f : α→α)
    (body : TM2ComputableInPolyTime e.toFinEncoding e.toFinEncoding f)
    (p : Polynomial ℕ)
    (sizeBound : ∀n a i,i≤n→(e.encode (f^[i] a)).length≤
      p.eval ((BitEncoding.unaryNat.prod e).encode (n,a)).length) :
    TM2ComputableInPolyTime (BitEncoding.unaryNat.prod e).toFinEncoding e.toFinEncoding
      (fun na=>f^[na.1] na.2):=by
  let time : Polynomial ℕ:=X*(C 2*p+C 3)+C 2
  let g:=body.toTM2ComputableAux
  refine {
    tm:=OracleSubstitution.machine machine g
    inputAlphabet:=machine.core.inputAlphabet
    outputAlphabet:=machine.core.outputAlphabet
    time:=OracleSubstitution.timePolynomial machine time body.time
    outputsFun:=?_}
  intro na
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost,hgood⟩:=run na.1 na.2
    (p.eval ((BitEncoding.unaryNat.prod e).encode na).length) (sizeBound na.1 na.2)
  have hN : ∀k,((machine.initial ((BitEncoding.unaryNat.prod e).encode na)).stk k).length≤
      ((BitEncoding.unaryNat.prod e).encode na).length:=OracleReductionComposition.initial_length machine _
  have hc : cost≤time.eval ((BitEncoding.unaryNat.prod e).encode na).length:=by
    apply hcost.trans
    have hn : na.1≤((BitEncoding.unaryNat.prod e).encode na).length:=by
      rw [BitEncoding.prod_length,BitEncoding.unaryNat_length]
      omega
    simpa only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C] using
      Nat.add_le_add_right (Nat.mul_le_mul_right (2*p.eval ((BitEncoding.unaryNat.prod e).encode na).length+3) hn) 2
  obtain ⟨t,ht,he⟩:=OracleSubstitution.compiled_run_on_trace machine g hr body.time
    (fun q a hqa=>by
      apply Classical.choice
      obtain ⟨x,hx⟩:=hgood (q,a) hqa
      have hq:=congrArg Prod.fst hx
      have ha:=congrArg Prod.snd hx
      dsimp only at hq ha
      subst q; subst a
      exact ⟨body.outputsFun x⟩) _ hN
  refine ⟨{steps:=t,evals_in_steps:=?_,steps_le_m:=?_}⟩
  · rw [OracleSubstitution.idle_initial,OracleSubstitution.idle_final] at he
    exact he
  · exact ht.trans (OracleReductionComposition.bound_polynomial machine time body.time
      ((BitEncoding.unaryNat.prod e).encode na).length cost hc)

end PlanarHom.BoundedIterationMachine
