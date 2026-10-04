import PlanarHom.ArithmeticCircuitPrimitives
import PlanarHom.ReturningBitSubroutine

/-! # Actual finite-control selection between two materialized typed values -/
namespace PlanarHom.ConditionalMachines
open Turing Turing.TM2 Complexity BinaryArithmetic

inductive Label | header | run (choose : Bool) (source : PairProjectionMachines.Label) | halt deriving DecidableEq,Fintype
abbrev State := PairProjectionMachines.State
abbrev Statement := Stmt (fun _ : Bool => Bool) Label State

def labels (b : Bool) : PairProjectionMachines.Label→Label := .run b

def program : Label→Statement
  | .header => .pop false (fun v _ => v) <| .pop false (fun v b => (v.1,b)) <|
      .pop false (fun v _ => v) <| .branch (fun v => v.2.getD false)
        (.load (fun _ => ((),none)) (.goto (fun _ => .run true .parse)))
        (.load (fun _ => ((),none)) (.goto (fun _ => .run false .parse)))
  | .run b l => ReturningBitSubroutine.compile (Function.Embedding.refl Bool) (labels b) (Equiv.refl State) .halt (PairProjectionMachines.program b (!b) l)
  | .halt => .halt

def machine : FinTM2 where
  K := Bool
  Γ _ := Bool
  k₀ := false
  k₁ := false
  Λ := Label
  main := .header
  σ := State
  initialState := ((),none)
  m := program

def cfg (l : Option Label) (xs scratch : Bits) : machine.Cfg := ⟨l,((),none),PairProjectionMachines.store xs scratch⟩

theorem header_step (b : Bool) (xs : Bits) :
    machine.step (cfg (some .header) (true::b::false::xs) []) = some (cfg (some (.run b .parse)) xs []) := by
  cases b <;> simp [machine,step,program,stepAux,cfg,PairProjectionMachines.store]

theorem halt_step (xs : Bits) : machine.step (cfg (some .halt) xs []) = some (cfg none xs []) := rfl

def projection_run (b : Bool) (xs ys : Bits) :
    EvalsToInTime machine.step (cfg (some (.run b .parse)) (BitEncoding.frame xs++ys) [])
      (some (cfg (some .halt) (if b then xs else ys) [])) ((BitEncoding.frame xs++ys).length+3) := by
  have hs : EvalsToInTime (step (PairProjectionMachines.program b (!b)))
      (PairProjectionMachines.config (some .parse) (BitEncoding.frame xs++ys) [])
      (some (PairProjectionMachines.config none (if b then xs else ys) [])) ((BitEncoding.frame xs++ys).length+3) := by
    cases b
    · simpa [TM2OutputsInTime,PairProjectionMachines.initial_config,PairProjectionMachines.final_config] using PairProjectionMachines.snd_outputs xs ys
    · simpa [TM2OutputsInTime,PairProjectionMachines.initial_config,PairProjectionMachines.final_config] using PairProjectionMachines.fst_outputs xs ys
  exact ReturningBitSubroutine.run (Function.Embedding.refl Bool) (labels b) (Equiv.refl State) .halt (fun _ => [])
    (PairProjectionMachines.program b (!b)) program (fun _ => rfl) _ _ _ _ _ hs
    (by refine ⟨rfl,rfl,?_,?_⟩; intro k; rfl; intro j hj; exact (hj j rfl).elim)
    (by refine ⟨rfl,rfl,?_,?_⟩; intro k; rfl; intro j hj; exact (hj j rfl).elim)

def outputs (b : Bool) (xs ys : Bits) :
    TM2OutputsInTime machine (true::b::false::(BitEncoding.frame xs++ys))
      (some (if b then xs else ys)) ((true::b::false::(BitEncoding.frame xs++ys)).length+2) := by
  have h₁ := oneStep machine.step (header_step b (BitEncoding.frame xs++ys))
  have h₂ := projection_run b xs ys
  have h₃ := oneStep machine.step (halt_step (if b then xs else ys))
  have h := EvalsToInTime.trans machine.step 1 _ _ _ _ h₁ h₂
  have h := EvalsToInTime.trans machine.step _ 1 _ _ _ h h₃
  have hi (word : Bits) : initList machine word=cfg (some .header) word [] := by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k; cases k <;> simp [machine,initList,cfg,PairProjectionMachines.store]
  have ho (word : Bits) : haltList machine word=cfg none word [] := by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k; cases k <;> simp [machine,haltList,cfg,PairProjectionMachines.store]
  change EvalsToInTime machine.step (initList machine _) (some (haltList machine _)) _
  rw [hi,ho]
  convert h using 1
  simp
  omega

noncomputable def computer {α : Type} (e : BitEncoding α) :
    TM2ComputableInPolyTime (BitEncoding.bool.prod (e.prod e)).toFinEncoding e.toFinEncoding
      (fun p => if p.1 then p.2.1 else p.2.2) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X+Polynomial.C 2
  outputsFun p := by
    simpa [BitEncoding.toFinEncoding,BitEncoding.prod,BitEncoding.bool,BitEncoding.frame,Equiv.refl,
      apply_ite e.encode] using outputs p.1 (e.encode p.2.1) (e.encode p.2.2)

theorem fp_select {α : Type} (e : BitEncoding α) :
    FP (BitEncoding.bool.prod (e.prod e)) e (fun p => if p.1 then p.2.1 else p.2.2) := ⟨computer e⟩

end PlanarHom.ConditionalMachines

namespace PlanarHom.Complexity

theorem FP.ite {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {p : α→Prop} [DecidablePred p] {f g : α→β}
    (hp : FP ea BitEncoding.bool (fun a => decide (p a))) (hf : FP ea eb f) (hg : FP ea eb g) :
    FP ea eb (fun a => if p a then f a else g a) := by
  exact ((hp.pair (hf.pair hg)).comp (ConditionalMachines.fp_select eb)).congr
    (fun a => by simp)

end PlanarHom.Complexity
