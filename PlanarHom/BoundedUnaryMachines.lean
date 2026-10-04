import PlanarHom.BoundedUnaryMachineCore
import PlanarHom.InputLengthMachine
import Mathlib.Tactic.Linarith

/-! Exact execution and polynomial cost of bounded unary expansion. -/
namespace PlanarHom.BoundedUnaryMachines
open Turing Turing.TM2 Polynomial PlanarHom.Complexity PlanarHom.MachineComposition
open PlanarHom.BinaryArithmetic

private theorem step_run (l next : Label) (hn : machine.request l=none) (d d' : Data)
    (hs : stepAux (program l) ((),none) d.get=cfg next d') :
    Runs (cfg l d) (cfg next d') 1:=ordinary hn (congrArg some hs)

private theorem parse_cons (d : Data) (b : Bool) (tail : Bits) :
    Runs (cfg .parse {d with input:=true::b::tail})
      (cfg .parse {d with input:=tail,bound:=true::d.bound}) 1:=by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem parse_nil (d : Data) (tail : Bits) :
    Runs (cfg .parse {d with input:=false::tail}) (cfg .check {d with input:=tail}) 1:=by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem unary_append_true (n : ℕ) (xs : Bits) :
    Computability.unaryEncodeNat n++true::xs=Computability.unaryEncodeNat (n+1)++xs:=by
  induction n with
  | zero=>rfl
  | succ n ih=>simpa only [Computability.unaryEncodeNat,List.cons_append] using congrArg (List.cons true) ih

theorem parse_run (d : Data) (F tail : Bits) :
    Runs (cfg .parse {d with input:=BitEncoding.frame F++tail})
      (cfg .check {d with input:=tail,bound:=Computability.unaryEncodeNat F.length++d.bound})
      (F.length+1):=by
  induction F generalizing d with
  | nil=>simpa [BitEncoding.frame,Computability.unaryEncodeNat] using parse_nil d tail
  | cons b F ih=>
    have h:=(parse_cons d b (BitEncoding.frame F++tail)).trans (ih {d with bound:=true::d.bound})
    simpa only [BitEncoding.frame,List.cons_append,List.length_cons,unary_append_true,Nat.add_comm] using h

private theorem check_empty (F out : Bits) :
    Runs (cfg .check ⟨[],F,out⟩) (cfg .clearBound ⟨[],F,out⟩) 1:=by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]

private theorem check_exhausted (xs out : Bits) (hx : xs≠[]) :
    Runs (cfg .check ⟨xs,[],out⟩) (cfg .clearInput ⟨xs,[],out⟩) 1:=by
  apply step_run _ _ rfl
  cases xs with
  | nil=>contradiction
  | cons b xs=>
    simp [program,resetGoto,stepAux,cfg,Data.get]
    funext k; cases k <;> rfl

private theorem check_more (xs F out : Bits) (b : Bool) (hx : xs≠[]) :
    Runs (cfg .check ⟨xs,b::F,out⟩) (cfg .query ⟨xs,F,out⟩) 1:=by
  apply step_run _ _ rfl
  cases xs with
  | nil=>contradiction
  | cons x xs=>
    simp [program,resetGoto,stepAux,cfg,Data.get]
    funext k; cases k <;> rfl

private theorem emit (d : Data) :
    Runs (cfg .emit d) (cfg .check {d with output:=true::d.output}) 1:=by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem finish (out : Bits) : Runs (cfg .halt ⟨[],[],out⟩) (machine.final out) 1:=by
  apply ordinary rfl
  apply congrArg some
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> simp [machine,program,stepAux,Data.get,OracleTM2.final,haltList,Equiv.refl]

private theorem clear_bound (F out : Bits) :
    Runs (cfg .clearBound ⟨[],F,out⟩) (machine.final out) (F.length+2):=by
  have h:=(clear .bound .clearBound .halt rfl rfl ⟨[],F,out⟩).trans (finish out)
  simpa [Data.get,Data.set,Nat.add_assoc] using h

/-- Each iteration consumes a cap marker, executes the actual predecessor
oracle, and emits one unary symbol. Every query and answer length is charged. -/
theorem loop_run (F out : Bits) (n L : ℕ) (hL : (BitEncoding.nat.encode n).length≤L) :
    Runs (cfg .check ⟨BitEncoding.nat.encode n,F,out⟩)
      (machine.final (Computability.unaryEncodeNat (min F.length n)++out))
      (F.length*(2*L+3)+L+F.length+4):=by
  induction F generalizing n out with
  | nil=>
    cases n with
    | zero=>
      have h:=(check_empty [] out).trans (clear_bound [] out)
      simpa [BitEncoding.nat,Computability.encodeNat,Computability.encodeNum,
        Computability.unaryEncodeNat] using h.mono (show 1+(0+2)≤L+4 by omega)
    | succ n=>
      have hn : BitEncoding.nat.encode (n+1)≠[]:=by
        simp [BitEncoding.nat,encodeNat_eq_nil]
      have h:=(check_exhausted (BitEncoding.nat.encode (n+1)) out hn).trans
        ((clear .input .clearInput .clearBound rfl rfl ⟨BitEncoding.nat.encode (n+1),[],out⟩).trans
          (clear_bound [] out))
      simp only [Data.get,List.length_nil] at h
      simpa [Computability.unaryEncodeNat] using h.mono (by omega)
  | cons b F ih=>
    cases n with
    | zero=>
      have h:=(check_empty (b::F) out).trans (clear_bound (b::F) out)
      simpa [BitEncoding.nat,Computability.encodeNat,Computability.encodeNum,
        Computability.unaryEncodeNat] using h.mono (by simp only [List.length_cons]; nlinarith)
    | succ n=>
      have hn : BitEncoding.nat.encode (n+1)≠[]:=by
        simp [BitEncoding.nat,encodeNat_eq_nil]
      have hl : (BitEncoding.nat.encode n).length≤L:=
        (encodeNat_length_mono (Nat.le_succ n)).trans hL
      have hq:=query_run ⟨BitEncoding.nat.encode (n+1),F,out⟩
      simp only [predecessor_encode,Nat.add_sub_cancel] at hq
      have hq':=hq.mono (show 1+(BitEncoding.nat.encode (n+1)).length+
          (BitEncoding.nat.encode n).length≤2*L+1 by omega)
      have h:=((check_more (BitEncoding.nat.encode (n+1)) F out b hn).trans hq').trans
        (emit ⟨BitEncoding.nat.encode n,F,out⟩)
      have hr:=h.trans (ih (true::out) n hl)
      have he : Computability.unaryEncodeNat (min F.length n)++true::out=
          Computability.unaryEncodeNat (min (b::F).length (n+1))++out:=by
        rw [unary_append_true,List.length_cons,min_add_add_right]
      rw [he] at hr
      exact hr.mono (by simp only [List.length_cons]; nlinarith)

def inputEncoding : BitEncoding (ℕ × ℕ):=BitEncoding.unaryNat.prod BitEncoding.nat
noncomputable def oracleTime : Polynomial ℕ:=C 10*(X+1)^2

theorem run (B n : ℕ) :
    Runs (machine.initial (inputEncoding.encode (B,n)))
      (machine.final (BitEncoding.unaryNat.encode (min B n)))
      (oracleTime.eval (inputEncoding.encode (B,n)).length):=by
  have hp:=parse_run ({} : Data) (BitEncoding.unaryNat.encode B) (BitEncoding.nat.encode n)
  simp only [List.append_nil,BitEncoding.unaryNat_length] at hp
  have hl:=loop_run (Computability.unaryEncodeNat B) [] n (BitEncoding.nat.encode n).length (by rfl)
  have hB : (Computability.unaryEncodeNat B).length=B:=BitEncoding.unaryNat_length B
  rw [hB,List.append_nil] at hl
  have hi : machine.initial (inputEncoding.encode (B,n))=
      cfg .parse {input:=BitEncoding.frame (BitEncoding.unaryNat.encode B)++BitEncoding.nat.encode n}:=by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k; cases k <;> simp [machine,OracleTM2.initial,initList,cfg,Data.get,inputEncoding,
        BitEncoding.prod,Equiv.refl]
  rw [hi]
  have h:=hp.trans hl
  apply h.mono
  simp only [oracleTime,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,inputEncoding,
    BitEncoding.prod_length,BitEncoding.unaryNat_length]
  nlinarith

/-- The output is capped by a unary input component, so no exponential unary
expansion is smuggled into polynomial-time computation. -/
noncomputable def computer :
    TM2ComputableInPolyTime inputEncoding.toFinEncoding BitEncoding.unaryNat.toFinEncoding
      (fun p=>min p.1 p.2):=by
  let g:=predecessorComputer.toTM2ComputableAux
  refine {
    tm:=OracleSubstitution.machine machine g
    inputAlphabet:=machine.core.inputAlphabet
    outputAlphabet:=machine.core.outputAlphabet
    time:=OracleSubstitution.timePolynomial machine oracleTime predecessorComputer.time
    outputsFun:=?_}
  intro p
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost⟩:=run p.1 p.2
  have hN : ∀k,((machine.initial (inputEncoding.encode p)).stk k).length≤
      (inputEncoding.encode p).length:=OracleReductionComposition.initial_length machine _
  obtain ⟨n,hn,he⟩:=OracleSubstitution.compiled_run machine g predecessorComputer.time
    (fun q=>predecessorComputer.outputsFun q) hr _ hN
  refine ⟨{steps:=n,evals_in_steps:=?_,steps_le_m:=?_}⟩
  · rw [OracleSubstitution.idle_initial,OracleSubstitution.idle_final] at he
    exact he
  · exact hn.trans (OracleReductionComposition.bound_polynomial machine oracleTime
      predecessorComputer.time (inputEncoding.encode p).length cost hcost)

end PlanarHom.BoundedUnaryMachines
