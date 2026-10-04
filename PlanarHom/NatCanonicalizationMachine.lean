import PlanarHom.OracleSubstitution
import PlanarHom.MachineOutputTransport
import Mathlib.Data.Num.Lemmas

/-! Actual normalization for the pinned mathlib natural decoder. A nonempty
word ending in `false` acquires a high `true`; this is not zero-padding removal. -/
namespace PlanarHom.NatCanonicalizationMachine
open Turing Turing.TM2 Polynomial PlanarHom.Complexity PlanarHom.MachineComposition

def suffix (xs : Bits) : Bits:=if xs.getLast?=some false then [true] else []
def canonical (xs : Bits) : Bits:=xs++suffix xs

private theorem positive_canonical (xs : Bits) (h : xs≠[]) :
    Computability.encodePosNum (Computability.decodePosNum xs)=canonical xs:=by
  induction xs using List.twoStepInduction with
  | nil=>contradiction
  | singleton b=>cases b <;> rfl
  | cons_cons b c xs _ ih=>
    have hh:=ih c (by simp)
    cases b with
    | false=>simpa [Computability.decodePosNum,Computability.encodePosNum,
        canonical,suffix,List.getLast?_cons_cons] using congrArg (List.cons false) hh
    | true=>simpa [Computability.decodePosNum,Computability.encodePosNum,
        canonical,suffix,List.getLast?_cons_cons] using congrArg (List.cons true) hh

theorem canonical_eq_encode_decode (xs : Bits) :
    canonical xs=BitEncoding.nat.encode (Computability.decodeNat xs):=by
  cases xs with
  | nil=>simp [canonical,suffix,BitEncoding.nat,Computability.decodeNat,Computability.decodeNum,Computability.encodeNat,Computability.encodeNum]
  | cons b xs=>
    simpa [BitEncoding.nat,Computability.encodeNat,Computability.decodeNat,
      Num.of_to_nat,Computability.decodeNum,Computability.encodeNum] using
      (positive_canonical (b::xs) (by simp)).symm

theorem canonical_length_le (xs : Bits) : (canonical xs).length≤xs.length+1:=by
  unfold canonical suffix
  split <;> simp

inductive Stack | input | buffer deriving DecidableEq, Fintype
inductive Label | scan | fix | restore | halt deriving DecidableEq, Fintype
abbrev State:=Unit × Option Bool
abbrev Statement:=Stmt (fun _ : Stack=>Bool) Label State
def resetGoto (l : Label) : Statement:=.load (fun _=>((),none)) (.goto (fun _=>l))
def program : Label→Statement
  | .scan=>transferStmt .input .buffer id id .scan .fix
  | .fix=>.peek .buffer (fun v a=>(v.1,a))
      (.branch (fun v=>v.2==some false)
        (.push .input (fun _=>true) (resetGoto .restore)) (resetGoto .restore))
  | .restore=>transferStmt .buffer .input id id .restore .halt
  | .halt=>.halt

def machine : FinTM2 where
  K:=Stack
  Γ:=fun _=>Bool
  k₀:=.input
  k₁:=.input
  Λ:=Label
  main:=.scan
  σ:=State
  initialState:=((),none)
  Γk₀Fin:=inferInstance
  m:=program

def store (xs ys : Bits) : Stack→Bits | .input=>xs | .buffer=>ys
def cfg (l : Label) (xs ys : Bits) : machine.Cfg:=⟨some l,((),none),store xs ys⟩
abbrev iter (n : ℕ) (c : machine.Cfg) : Option machine.Cfg:=
  (fun c : Option machine.Cfg=>c.bind machine.step)^[n] (some c)

theorem scan_run (xs : Bits) :
    iter (xs.length+1) (cfg .scan xs [])=some (cfg .fix [] xs.reverse):=by
  have h:=transfer_run program Stack.input Stack.buffer (by decide) id id Label.scan Label.fix
    rfl () none (store xs [])
  have hs : transferStore Stack.input Stack.buffer (id : Bool→Bool) (store xs [])=store [] xs.reverse:=by
    funext k; cases k <;> simp [transferStore,store]
  simpa [iter,machine,FinTM2.step,cfg,store,Function.comp_def,hs] using h

theorem fix_run (xs : Bits) :
    iter 1 (cfg .fix [] xs.reverse)=some (cfg .restore (suffix xs) xs.reverse):=by
  have hh : xs.reverse.head?=xs.getLast?:=List.head?_reverse
  by_cases h:xs.getLast?=some false
  · simp [iter,machine,FinTM2.step,step,program,stepAux,cfg,store,resetGoto,suffix,hh,h]
    funext k; cases k <;> rfl
  · have hb : (xs.getLast? == some false)=false:=by simpa only [beq_eq_false_iff_ne] using h
    simp [iter,machine,FinTM2.step,step,program,stepAux,cfg,store,resetGoto,suffix,hh,h,hb]

theorem restore_run (xs ys : Bits) :
    iter (ys.length+1) (cfg .restore xs ys)=some (cfg .halt (ys.reverse++xs) []):=by
  have h:=transfer_run program Stack.buffer Stack.input (by decide) id id Label.restore Label.halt
    rfl () none (store xs ys)
  have hs : transferStore Stack.buffer Stack.input (id : Bool→Bool) (store xs ys)=store (ys.reverse++xs) []:=by
    funext k; cases k <;> simp [transferStore,store]
  simpa [iter,machine,FinTM2.step,cfg,store,Function.comp_def,hs] using h

theorem halt_run (xs : Bits) : iter 1 (cfg .halt xs [])=some (haltList machine xs):=by
  apply congrArg some
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> simp [machine,program,stepAux,store,haltList]

theorem run (xs : Bits) :
    (fun c : Option machine.Cfg=>c.bind machine.step)^[2*xs.length+4]
      (some (initList machine xs))=some (haltList machine (canonical xs)):=by
  have hi : initList machine xs=cfg .scan xs []:=by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k; cases k <;> rfl
  have h₁:=scan_run xs
  have h₂:=fix_run xs
  have h₃:=restore_run (suffix xs) xs.reverse
  simp only [List.length_reverse,List.reverse_reverse] at h₃
  have h₄:=halt_run (canonical xs)
  have trans {n k : ℕ} {a b c : machine.Cfg}
      (h : iter n a=some b) (h' : iter k b=some c) : iter (k+n) a=some c:=by
    unfold iter at h h' ⊢
    rw [Function.iterate_add_apply,h,h']
  have h:=trans (trans (trans h₁ h₂) h₃) h₄
  rw [hi]
  unfold iter at h
  convert h using 1
  congr 1
  omega


/-- Correct on every raw word, including the noncanonical one-bit word `[false]`. -/
noncomputable def computer :
    TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding BitEncoding.bits.toFinEncoding canonical where
  tm:=machine
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=C 2*X+C 4
  outputsFun xs:={
    steps:=2*xs.length+4
    evals_in_steps:=by simpa [BitEncoding.bits,BitEncoding.toFinEncoding,Equiv.refl] using run xs
    steps_le_m:=by simp [BitEncoding.bits,BitEncoding.toFinEncoding] }

/-- The natural decoder itself is compiled, with its canonical binary output. -/
noncomputable def decodeComputer :
    TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding BitEncoding.nat.toFinEncoding
      Computability.decodeNat:=
  transportOutputComputer BitEncoding.bits BitEncoding.bits BitEncoding.nat
    canonical_eq_encode_decode computer

end PlanarHom.NatCanonicalizationMachine
