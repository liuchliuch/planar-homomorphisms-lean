import PlanarHom.OracleSubstitution

/-! Actual unary measurement of an input codeword, with one transition per bit. -/

namespace PlanarHom.InputLengthMachine
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition

inductive Stack | input | output deriving DecidableEq, Fintype
inductive Label | scan | halt deriving DecidableEq, Fintype

def machine : FinTM2 where
  K:=Stack
  Γ:=fun _=>Bool
  k₀:=.input
  k₁:=.output
  Λ:=Label
  main:=.scan
  σ:=Unit × Option Bool
  initialState:=((),none)
  Γk₀Fin:=inferInstance
  m | .scan => transferStmt .input .output id (fun _=>true) .scan .halt
    | .halt => .halt

def store (xs ys : Bits) : Stack→Bits | .input=>xs | .output=>ys

@[simp] theorem unary_eq_replicate (n : ℕ) :
    Computability.unaryEncodeNat n=List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Computability.unaryEncodeNat,List.replicate_succ] using congrArg (List.cons true) ih

theorem mapped_reverse (xs : Bits) :
    (xs.map (fun _=>true)).reverse=Computability.unaryEncodeNat xs.length := by
  simp [unary_eq_replicate]

theorem run (xs : Bits) :
    (fun c : Option machine.Cfg=>c.bind machine.step)^[xs.length+2]
      (some (initList machine xs))=
        some (haltList machine (Computability.unaryEncodeNat xs.length)) := by
  have h:=transfer_run machine.m Stack.input Stack.output (by intro h; cases h)
    id (fun _=>true) Label.scan Label.halt rfl () none (store xs [])
  have hi : initList machine xs=⟨some .scan,((),none),store xs []⟩ := by
    apply OracleSubstitution.cfg_ext <;> try rfl
    funext k; cases k <;> rfl
  have hs : transferStore Stack.input Stack.output (fun _ : Bool=>true) (store xs [])=
      store [] (Computability.unaryEncodeNat xs.length) := by
    funext k; cases k <;> simp [transferStore,store]
  rw [hi]
  rw [show xs.length+2=1+(xs.length+1) by omega]
  rw [Function.iterate_add_apply]
  have hr : (fun c : Option machine.Cfg=>c.bind machine.step)^[xs.length+1]
      (some ⟨some .scan,((),none),store xs []⟩)=
        some ⟨some .halt,((),none),store [] (Computability.unaryEncodeNat xs.length)⟩ := by
    simpa [store,FinTM2.step,Function.comp_def,hs] using h
  rw [hr]
  change some (stepAux (machine.m .halt) ((),none) (store [] (Computability.unaryEncodeNat xs.length))) = _
  congr 1
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> simp [machine,store,stepAux,haltList]

/-- This outputs unary input length for any typed code, not a binary-to-unary
conversion without a size bound. -/
noncomputable def computer {α : Type} (ea : BitEncoding α) :
    TM2ComputableInPolyTime ea.toFinEncoding BitEncoding.unaryNat.toFinEncoding
      (fun a=>(ea.encode a).length) where
  tm:=machine
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=Polynomial.X+Polynomial.C 2
  outputsFun a:={
    steps:=(ea.encode a).length+2
    evals_in_steps:=by simpa [BitEncoding.toFinEncoding,BitEncoding.unaryNat,Equiv.refl] using run (ea.encode a)
    steps_le_m:=by simp [BitEncoding.toFinEncoding] }

end PlanarHom.InputLengthMachine
