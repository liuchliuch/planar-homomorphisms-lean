import PlanarHom.MachinePairing

/-! Real finite-control constant-output machines and operand constants. -/

namespace PlanarHom.ConstantMachines
open Turing Turing.TM2 PlanarHom.Complexity

/-- Static code pushes a fixed word in its original order. -/
def pushWord : Bits → Stmt (fun _ : Unit=>Bool) Unit (Option Bool) → Stmt (fun _ : Unit=>Bool) Unit (Option Bool)
  | [], next => next
  | b::bs, next => pushWord bs (.push () (fun _=>b) next)

theorem pushWord_correct (w xs : Bits) (next : Stmt (fun _ : Unit=>Bool) Unit (Option Bool)) (v : Option Bool) :
    stepAux (pushWord w next) v (fun _=>xs) = stepAux next v (fun _=>w++xs) := by
  induction w generalizing next with
  | nil => rfl
  | cons b bs ih =>
    rw [pushWord,ih]
    change stepAux next v (Function.update (fun _=>bs++xs) () (b::(bs++xs))) = _
    congr 1

def machine (out : Bits) : FinTM2 where
  K:=Unit
  Γ:=fun _=>Bool
  k₀:=()
  k₁:=()
  Λ:=Unit
  main:=()
  σ:=Option Bool
  initialState:=none
  Γk₀Fin:=inferInstance
  m _ := .pop () (fun _ a=>a) (.branch Option.isSome (.goto (fun _=>()))
    (.load (fun _=>none) (pushWord out .halt)))

def cfg (l : Option Unit) (v : Option Bool) (xs : Bits) : Cfg (fun _ : Unit=>Bool) Unit (Option Bool) :=
  ⟨l,v,fun _=>xs⟩

theorem step_nil (out : Bits) (v : Option Bool) :
    (machine out).step (cfg (some ()) v [])=some (cfg none none out) := by
  simp only [machine,FinTM2.step,step,stepAux,cfg,List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
  have hu : Function.update (fun _ : Unit=>([] : Bits)) () [] = (fun _=>[]) := by funext k; cases k; rfl
  rw [hu,pushWord_correct]
  simp [stepAux]

theorem step_cons (out : Bits) (v : Option Bool) (b : Bool) (xs : Bits) :
    (machine out).step (cfg (some ()) v (b::xs))=some (cfg (some ()) (some b) xs) := by
  simp [machine,FinTM2.step,step,stepAux,cfg]
  funext k; cases k; rfl

theorem run (out xs : Bits) (v : Option Bool) :
    (fun c : Option (machine out).Cfg=>c.bind (machine out).step)^[xs.length+1]
      (some (cfg (some ()) v xs))=some (cfg none none out) := by
  induction xs generalizing v with
  | nil => exact step_nil out v
  | cons b xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change (fun c : Option (machine out).Cfg=>c.bind (machine out).step)^[xs.length+1]
      ((machine out).step (cfg (some ()) v (b::xs))) = _
    rw [step_cons]
    exact ih (some b)

/-- A fixed output codeword is emitted after explicitly clearing the entire input. -/
noncomputable def computer {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (b : β) :
    TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding (fun _=>b) where
  tm:=machine (eb.encode b)
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=Polynomial.X+1
  outputsFun a := {
    steps:=(ea.encode a).length+1
    evals_in_steps:=by
      have hi : initList (machine (eb.encode b)) (ea.encode a)=cfg (some ()) none (ea.encode a) := by
        apply OracleSubstitution.cfg_ext
        · rfl
        · rfl
        · funext k; cases k; rfl
      have ho : haltList (machine (eb.encode b)) (eb.encode b)=cfg none none (eb.encode b) := by
        apply OracleSubstitution.cfg_ext
        · rfl
        · rfl
        · funext k; cases k; rfl
      simpa [BitEncoding.toFinEncoding,Equiv.refl,hi,ho] using run (eb.encode b) (ea.encode a) none
    steps_le_m:=by simp [BitEncoding.toFinEncoding] }

end PlanarHom.ConstantMachines

namespace PlanarHom.Complexity

theorem fp_const {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (b : β) :
    FP ea eb (fun _=>b) := ⟨ConstantMachines.computer ea eb b⟩

end PlanarHom.Complexity
