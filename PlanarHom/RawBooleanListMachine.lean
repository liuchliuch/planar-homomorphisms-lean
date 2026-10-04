import PlanarHom.InputLengthMachine
import PlanarHom.UnaryNatConversionMachine
import PlanarHom.PairProjectionMachines

/-! NEW reconstruction: raw Boolean words to framed Boolean lists, with a
literal linear-time transducer and a real binary length-header compiler. -/

namespace PlanarHom.RawBooleanListMachine

open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition

def payload : Bits → Bits
  | [] => []
  | b::bs => true::b::false::payload bs

@[simp] theorem payload_length (xs : Bits) : (payload xs).length=3*xs.length := by
  induction xs <;> simp [payload, *] <;> omega

inductive Stack | input | buffer | output
  deriving DecidableEq, Fintype
inductive Label | scan | reverse | finish
  deriving DecidableEq, Fintype

def store (xs buf out : Bits) : Stack → Bits
  | .input => xs
  | .buffer => buf
  | .output => out

def program : Label → Stmt (fun _ : Stack => Bool) Label (Unit × Option Bool)
  | .scan => .pop .input (fun v a => (v.1,a))
      (.branch (fun v => v.2.isSome)
        (.push .buffer (fun _=>true) (.push .buffer (fun v=>v.2.getD false)
          (.push .buffer (fun _=>false) (.load (fun v=>(v.1,none)) (.goto (fun _=>.scan))))))
        (.load (fun v=>(v.1,none)) (.goto (fun _=>.reverse))))
  | .reverse => transferStmt .buffer .output id id .reverse .finish
  | .finish => .halt

def machine : FinTM2 where
  K := Stack
  Γ := fun _ => Bool
  k₀ := .input
  k₁ := .output
  Λ := Label
  main := .scan
  σ := Unit × Option Bool
  initialState := ((),none)
  Γk₀Fin := inferInstance
  m := program

def cfg (l : Label) (xs buf out : Bits) : machine.Cfg :=
  ⟨some l,((),none),store xs buf out⟩

abbrev iter (n : ℕ) (c : machine.Cfg) : Option machine.Cfg :=
  (fun c : Option machine.Cfg => c.bind machine.step)^[n] (some c)

theorem step_scan_nil (buf out : Bits) :
    machine.step (cfg .scan [] buf out) = some (cfg .reverse [] buf out) := by
  simp only [machine,FinTM2.step,cfg,step,program,stepAux,store,List.head?_nil,
    Option.isSome_none,Bool.cond_false,List.tail_nil]
  congr 2
  funext k
  cases k <;> simp [store]

theorem step_scan_cons (x : Bool) (xs buf out : Bits) :
    machine.step (cfg .scan (x::xs) buf out) = some (cfg .scan xs (false::x::true::buf) out) := by
  simp only [machine,FinTM2.step,cfg,step,program,stepAux,store,List.head?_cons,
    Option.isSome_some,Bool.cond_true,List.tail_cons,Option.getD_some]
  congr 2
  funext k
  cases k <;> simp [store]

/-- Every input bit emits its literal three-bit singleton frame. -/
theorem scan_run (xs buf out : Bits) :
    iter (xs.length+1) (cfg .scan xs buf out) =
      some (cfg .reverse [] ((payload xs).reverse++buf) out) := by
  induction xs generalizing buf with
  | nil => simpa [iter,payload] using step_scan_nil buf out
  | cons x xs ih =>
    change (fun c : Option machine.Cfg => c.bind machine.step)^[xs.length+1+1]
      (some (cfg .scan (x::xs) buf out)) = _
    rw [Function.iterate_succ_apply]
    change (fun c : Option machine.Cfg => c.bind machine.step)^[xs.length+1]
      (machine.step (cfg .scan (x::xs) buf out)) = _
    rw [step_scan_cons]
    simpa [payload,List.reverse_cons,List.append_assoc] using ih (false::x::true::buf)

theorem transfer_store (xs buf out : Bits) :
    transferStore .buffer .output (id : Bool→Bool) (store xs buf out) =
      store xs [] (buf.reverse++out) := by
  funext k
  cases k <;> simp [transferStore,store]

theorem reverse_run (buf : Bits) :
    iter (buf.length+1) (cfg .reverse [] buf []) = some (cfg .finish [] [] buf.reverse) := by
  have h := transfer_run program Stack.buffer Stack.output (by intro h; cases h)
    id id Label.reverse Label.finish rfl () none (store [] buf [])
  simpa [iter,cfg,FinTM2.step,machine,transfer_store] using h

theorem finish_run (out : Bits) : machine.step (cfg .finish [] [] out) =
    some (haltList machine out) := by
  apply congrArg some
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [machine,program,stepAux,haltList,store]

theorem initial_eq (xs : Bits) : initList machine xs = cfg .scan xs [] [] := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [initList,machine,cfg,store]

/-- Exact end-to-end iteration, including reversal, cleanup, and final halt. -/
theorem payload_run (xs : Bits) :
    (fun c : Option machine.Cfg => c.bind machine.step)^[4*xs.length+3]
      (some (initList machine xs)) = some (haltList machine (payload xs)) := by
  have h₁ : iter (xs.length+1) (cfg .scan xs [] []) =
      some (cfg .reverse [] (payload xs).reverse []) := by
    simpa only [List.append_nil] using scan_run xs [] []
  have h₂ : iter ((payload xs).reverse.length+1)
      (cfg .reverse [] (payload xs).reverse []) =
      some (cfg .finish [] [] (payload xs)) := by
    simpa only [List.reverse_reverse] using reverse_run (payload xs).reverse
  have h₃ : iter 1 (cfg .finish [] [] (payload xs)) =
      some (haltList machine (payload xs)) := finish_run (payload xs)
  have hlen : 1+(((payload xs).reverse.length+1)+(xs.length+1)) = 4*xs.length+3 := by
    simp only [List.length_reverse,payload_length]
    omega
  unfold iter at h₁ h₂ h₃
  rw [initial_eq,←hlen]
  rw [Function.iterate_add_apply,Function.iterate_add_apply,h₁,h₂]
  exact h₃


/-- A real linear-time machine emits the Boolean-list payload. -/
noncomputable def payloadComputer : TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding
    BitEncoding.bits.toFinEncoding payload where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 4 * Polynomial.X + Polynomial.C 3
  outputsFun xs := {
    steps := 4*xs.length+3
    evals_in_steps := by
      change (fun c : Option machine.Cfg => c.bind machine.step)^[4*xs.length+3]
        (some (initList machine (xs.map id))) =
          some (haltList machine ((payload xs).map id))
      simpa only [List.map_id] using payload_run xs
    steps_le_m := by simp [BitEncoding.toFinEncoding,BitEncoding.bits] }

theorem fp_payload : FP BitEncoding.bits BitEncoding.bits payload := ⟨payloadComputer⟩

theorem payload_eq_frames (xs : Bits) : payload xs=BitEncoding.frames (xs.map BitEncoding.bool.encode) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [payload,BitEncoding.frames,BitEncoding.frame,BitEncoding.bool,ih]

/-- Canonical binary list framing is actually constructed from the raw input. -/
theorem fp_boolList : FP BitEncoding.bits BitEncoding.bool.list id := by
  have hn : FP BitEncoding.bits BitEncoding.nat (fun xs : Bits => xs.length) :=
    (show FP BitEncoding.bits BitEncoding.unaryNat (fun xs : Bits => xs.length) from
      ⟨InputLengthMachine.computer BitEncoding.bits⟩).comp UnaryNatConversionMachine.fp_conversion
  have h := hn.pair fp_payload
  apply h.transportOutput
  intro xs
  simp only [BitEncoding.prod,BitEncoding.bits,BitEncoding.list,payload_eq_frames,Function.comp_apply,id_eq]

end PlanarHom.RawBooleanListMachine
