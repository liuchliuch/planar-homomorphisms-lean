import PlanarHom.OracleSubstitution

/-! Actual linear-time TM2 construction of the escaped-word frame codec. -/

namespace PlanarHom.FrameMachines

open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition

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
          (.load (fun v=>(v.1,none)) (.goto (fun _=>.scan)))))
        (.push .buffer (fun _=>false) (.load (fun v=>(v.1,none)) (.goto (fun _=>.reverse)))))
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
    machine.step (cfg .scan [] buf out) = some (cfg .reverse [] (false::buf) out) := by
  simp only [machine,FinTM2.step,cfg,step,program,stepAux,store,List.head?_nil,
    Option.isSome_none,Bool.cond_false,List.tail_nil]
  congr 2
  funext k
  cases k <;> simp [store]

theorem step_scan_cons (x : Bool) (xs buf out : Bits) :
    machine.step (cfg .scan (x::xs) buf out) = some (cfg .scan xs (x::true::buf) out) := by
  simp only [machine,FinTM2.step,cfg,step,program,stepAux,store,List.head?_cons,
    Option.isSome_some,Bool.cond_true,List.tail_cons,Option.getD_some]
  congr 2
  funext k
  cases k <;> simp [store]

/-- One transition per input bit adds its two framing bits, and one transition
adds the terminal delimiter. The buffer is reversed to avoid any free append. -/
theorem scan_run (xs buf out : Bits) :
    iter (xs.length+1) (cfg .scan xs buf out) =
      some (cfg .reverse [] ((BitEncoding.frame xs).reverse++buf) out) := by
  induction xs generalizing buf with
  | nil => simpa [iter,BitEncoding.frame] using step_scan_nil buf out
  | cons x xs ih =>
    change (fun c : Option machine.Cfg => c.bind machine.step)^[xs.length+1+1]
      (some (cfg .scan (x::xs) buf out)) = _
    rw [Function.iterate_succ_apply]
    change (fun c : Option machine.Cfg => c.bind machine.step)^[xs.length+1]
      (machine.step (cfg .scan (x::xs) buf out)) = _
    rw [step_scan_cons]
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc] using ih (x::true::buf)

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
theorem frame_run (xs : Bits) :
    (fun c : Option machine.Cfg => c.bind machine.step)^[3*xs.length+4]
      (some (initList machine xs)) = some (haltList machine (BitEncoding.frame xs)) := by
  have h₁ : iter (xs.length+1) (cfg .scan xs [] []) =
      some (cfg .reverse [] (BitEncoding.frame xs).reverse []) := by
    simpa only [List.append_nil] using scan_run xs [] []
  have h₂ : iter ((BitEncoding.frame xs).reverse.length+1)
      (cfg .reverse [] (BitEncoding.frame xs).reverse []) =
      some (cfg .finish [] [] (BitEncoding.frame xs)) := by
    simpa only [List.reverse_reverse] using reverse_run (BitEncoding.frame xs).reverse
  have h₃ : iter 1 (cfg .finish [] [] (BitEncoding.frame xs)) =
      some (haltList machine (BitEncoding.frame xs)) := finish_run (BitEncoding.frame xs)
  have hlen : 1+(((BitEncoding.frame xs).reverse.length+1)+(xs.length+1)) = 3*xs.length+4 := by
    simp only [List.length_reverse,BitEncoding.frame_length]
    omega
  unfold iter at h₁ h₂ h₃
  rw [initial_eq,←hlen]
  rw [Function.iterate_add_apply,Function.iterate_add_apply,h₁,h₂]
  exact h₃


/-- The escaped-word encoder is an actual linear-time TM2 computer over raw
bits, with all intermediate stacks emptied and finite control reset. -/
noncomputable def frameComputer : TM2ComputableInPolyTime BitEncoding.bits.toFinEncoding
    BitEncoding.bits.toFinEncoding BitEncoding.frame where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 4
  outputsFun xs := {
    steps := 3*xs.length+4
    evals_in_steps := by
      change (fun c : Option machine.Cfg => c.bind machine.step)^[3*xs.length+4]
        (some (initList machine (xs.map id))) =
          some (haltList machine ((BitEncoding.frame xs).map id))
      simpa only [List.map_id] using frame_run xs
    steps_le_m := by simp [BitEncoding.toFinEncoding,BitEncoding.bits] }

theorem fp_frame : FP BitEncoding.bits BitEncoding.bits BitEncoding.frame := ⟨frameComputer⟩

end PlanarHom.FrameMachines
