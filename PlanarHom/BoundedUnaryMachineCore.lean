import PlanarHom.ConstantMachines
import PlanarHom.BinarySubtractionMachine
import PlanarHom.BinaryGcdBits
import PlanarHom.OracleReductionComposition

/-! A size-honest binary-to-unary converter, bounded by an explicitly unary cap. -/
namespace PlanarHom.BoundedUnaryMachines
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition
open PlanarHom.BinaryArithmetic

/-- This oracle uses padded-bit arithmetic on arbitrary words; its typed
canonical-input behavior is proved separately below. -/
def predecessorBits (xs : Bits) : Bits := subBits xs [true]

@[simp] theorem predecessor_encode (n : ℕ) :
    predecessorBits (BitEncoding.nat.encode n)=BitEncoding.nat.encode (n-1) := by
  simpa [predecessorBits,BitEncoding.nat,Computability.encodeNat,Computability.encodeNum,Computability.encodePosNum] using subBits_encodeNat n 1

noncomputable def subtractionRawComputer :
    TM2ComputableInPolyTime (BitEncoding.bits.prod BitEncoding.bits).toFinEncoding
      BitEncoding.bits.toFinEncoding (fun p=>subBits p.1 p.2) where
  tm:=subtractionMachine false
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=Polynomial.C 2*Polynomial.X+Polynomial.C 2
  outputsFun p:=by
    have h:=subtraction_outputs false p.1 p.2
    have ht : 4*p.1.length+2*p.2.length+4=2*(2*p.1.length+p.2.length+1)+2 := by omega
    rw [ht] at h
    simpa [BitEncoding.toFinEncoding,BitEncoding.prod,BitEncoding.bits,BitEncoding.frame_length,
      subBits,subtractionResult,Equiv.refl,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

/-- Actual ordinary machine for every oracle query, including noncanonical words. -/
noncomputable def predecessorComputer :
    TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding BitEncoding.bits.toFinEncoding predecessorBits :=
  composeComputers
    (PlanarHom.MachinePairing.pairComputers
      (idComputableInPolyTime BitEncoding.bits.toFinEncoding)
      (PlanarHom.ConstantMachines.computer BitEncoding.bits BitEncoding.bits [true]))
    subtractionRawComputer

inductive Stack | input | bound | output deriving DecidableEq, Fintype
inductive Label | parse | check | query | emit | clearInput | clearBound | halt
  deriving DecidableEq, Fintype
structure Data where
  input : Bits:=[]
  bound : Bits:=[]
  output : Bits:=[]
def Data.get (d : Data) : Stack→Bits
  | .input=>d.input | .bound=>d.bound | .output=>d.output
def Data.set (d : Data) (k : Stack) (xs : Bits) : Data := match k with
  | .input=>{d with input:=xs} | .bound=>{d with bound:=xs} | .output=>{d with output:=xs}
@[simp] theorem update_get (d : Data) (k : Stack) (xs : Bits) :
    Function.update d.get k xs=(d.set k xs).get := by
  funext j; cases j <;> cases k <;> simp [Data.get,Data.set]

abbrev State:=Unit × Option Bool
abbrev Statement:=Stmt (fun _ : Stack=>Bool) Label State
def resetGoto (l : Label) : Statement:=.load (fun _=>((),none)) (.goto (fun _=>l))
def program : Label→Statement
  | .parse=>.pop .input (fun v a=>(v.1,a))
      (.branch (fun v=>v.2.getD false)
        (.pop .input (fun v a=>(v.1,a)) (.push .bound (fun _=>true) (resetGoto .parse)))
        (resetGoto .check))
  | .check=>.peek .input (fun v a=>(v.1,a))
      (.branch (fun v=>v.2.isSome)
        (.pop .bound (fun v a=>(v.1,a))
          (.branch (fun v=>v.2.isSome) (resetGoto .query) (resetGoto .clearInput)))
        (resetGoto .clearBound))
  | .query=>.halt
  | .emit=>.push .output (fun _=>true) (resetGoto .check)
  | .clearInput=>clearStmt .input .clearInput .clearBound
  | .clearBound=>clearStmt .bound .clearBound .halt
  | .halt=>.halt

def machine : OracleTM2 where
  core := {
    tm := {
      K := Stack
      Γ := fun _=>Bool
      k₀ := .input
      k₁ := .output
      Λ := Label
      main := .parse
      σ := State
      initialState := ((),none)
      Γk₀Fin := inferInstance
      m := program }
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool }
  finiteAlphabet:=fun _=>inferInstance
  queryStack:=.input
  answerStack:=.input
  queryAlphabet:=Equiv.refl Bool
  answerAlphabet:=Equiv.refl Bool
  request | .query=>some .emit | _=>none

def cfg (l : Label) (d : Data) : machine.Cfg:=⟨some l,((),none),d.get⟩
def Runs (c d : machine.Cfg) (bound : ℕ) : Prop:=
  ∃s t qs,machine.Run predecessorBits c d s t qs ∧ t≤bound

theorem Runs.refl (c : machine.Cfg) : Runs c c 0:=⟨0,0,[],.refl c,by rfl⟩
theorem Runs.trans {c d e : machine.Cfg} {n k : ℕ} (h : Runs c d n) (h' : Runs d e k) :
    Runs c e (n+k):=by
  obtain ⟨s,t,qs,hr,ht⟩:=h
  obtain ⟨s',t',qs',hr',ht'⟩:=h'
  exact ⟨_,_,_,hr.trans hr',Nat.add_le_add ht ht'⟩
theorem Runs.mono {c d : machine.Cfg} {n k : ℕ} (h : Runs c d n) (hk : n≤k) : Runs c d k:=by
  obtain ⟨s,t,qs,hr,ht⟩:=h
  exact ⟨s,t,qs,hr,ht.trans hk⟩
theorem ordinary {c d : machine.Cfg} (hn : machine.continuation c=none)
    (hs : machine.core.tm.step c=some d) : Runs c d 1:=⟨1,1,[],.ordinary hn hs (.refl d),by rfl⟩
theorem ordinary_label (l : Label) (hn : machine.request l=none) (v : State) (S : Stack→Bits) :
    Runs ⟨some l,v,S⟩ (stepAux (program l) v S) 1:=ordinary hn rfl

theorem clear (i : Stack) (loop next : Label) (hp : program loop=clearStmt i loop next)
    (hn : machine.request loop=none) (d : Data) :
    Runs (cfg loop d) (cfg next (d.set i [])) ((d.get i).length+1):=by
  have h:=clear_rel Runs (@Runs.trans) i loop next
    (fun v r S=>by rw [←hp]; exact ordinary_label loop hn (v,r) S) () none d.get
  simpa [cfg,machine] using h

theorem query_run (d : Data) :
    Runs (cfg .query d) (cfg .emit {d with input:=predecessorBits d.input})
      (1+d.input.length+(predecessorBits d.input).length):=by
  have hq : machine.continuation (cfg .query d)=some .emit:=rfl
  have hw : machine.queryWord (cfg .query d)=d.input:=by
    simp [machine,OracleTM2.queryWord,cfg,Data.get,Equiv.refl]
  have he : machine.answerCfg predecessorBits (cfg .query d) .emit=
      cfg .emit {d with input:=predecessorBits d.input}:=by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · simp [OracleTM2.answerCfg,machine,OracleTM2.queryWord,cfg,Equiv.refl,Data.get]
      funext k; cases k <;> rfl
  refine ⟨1,_,[(d.input,predecessorBits d.input)],?_,Nat.le_refl _⟩
  have h:=OracleTM2.Run.query (m:=machine) (oracle:=predecessorBits) Label.emit hq
    (OracleTM2.Run.refl (machine.answerCfg predecessorBits (cfg .query d) .emit))
  simpa only [he,hw,Nat.zero_add] using h

end PlanarHom.BoundedUnaryMachines
