import PlanarHom.BoundedIterationMachine
import PlanarHom.ConstantMachines
import PlanarHom.MachineOutputTransport

/-! Actual bounded iteration with a restricted, honestly serialized initial
state. This supports fixed seeds such as1 for powers without requiring bounds
for arbitrary unreachable accumulator values. -/
namespace PlanarHom.BoundedIterationMachine
open Turing Polynomial PlanarHom.Complexity PlanarHom.MachineComposition PlanarHom.MachinePairing

/-- Reuse the actual iterator when the source representation literally contains
its unary iteration count followed by the initial state codeword. The views
`count` and `start` do not execute as host-language functions. -/
noncomputable def computerOn {α β : Type} (input : BitEncoding β) (e : BitEncoding α)
    (f : α→α) (count : β→ℕ) (start : β→α)
    (sameWords : ∀b,input.encode b=(BitEncoding.unaryNat.prod e).encode (count b,start b))
    (body : TM2ComputableInPolyTime e.toFinEncoding e.toFinEncoding f)
    (p : Polynomial ℕ)
    (sizeBound : ∀b i,i≤count b→(e.encode (f^[i] (start b))).length≤p.eval (input.encode b).length) :
    TM2ComputableInPolyTime input.toFinEncoding e.toFinEncoding (fun b=>f^[count b] (start b)):=by
  let time : Polynomial ℕ:=X*(C 2*p+C 3)+C 2
  let g:=body.toTM2ComputableAux
  refine {
    tm:=OracleSubstitution.machine machine g
    inputAlphabet:=machine.core.inputAlphabet
    outputAlphabet:=machine.core.outputAlphabet
    time:=OracleSubstitution.timePolynomial machine time body.time
    outputsFun:=?_}
  intro b
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost,hgood⟩:=run (count b) (start b)
    (p.eval (input.encode b).length) (sizeBound b)
  rw [←sameWords b] at hr
  have hN : ∀k,((machine.initial (input.encode b)).stk k).length≤(input.encode b).length:=
    OracleReductionComposition.initial_length machine _
  have hc : cost≤time.eval (input.encode b).length:=by
    apply hcost.trans
    have hn : count b≤(input.encode b).length:=by
      rw [sameWords,BitEncoding.prod_length,BitEncoding.unaryNat_length]
      omega
    simpa only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C] using
      Nat.add_le_add_right (Nat.mul_le_mul_right (2*p.eval (input.encode b).length+3) hn) 2
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
      (input.encode b).length cost hc)

/-- The initial constant is physically present in this internal representation. -/
def seedEncoding {α : Type} (e : BitEncoding α) (a : α) : BitEncoding ℕ:=
  (BitEncoding.unaryNat.prod e).retract (fun n=>(n,a)) Prod.fst (by intro n; rfl)

/-- A fixed seed is assembled by real pairing and constant-output machines,
then the real iterator runs with its bound restricted to that seed. -/
noncomputable def fromSeedComputer {α : Type} (e : BitEncoding α) (f : α→α) (a : α)
    (body : TM2ComputableInPolyTime e.toFinEncoding e.toFinEncoding f)
    (p : Polynomial ℕ) (sizeBound : ∀n i,i≤n→(e.encode (f^[i] a)).length≤p.eval n) :
    TM2ComputableInPolyTime BitEncoding.unaryNat.toFinEncoding e.toFinEncoding (fun n=>f^[n] a):=by
  let prepare:=pairComputers (idComputableInPolyTime BitEncoding.unaryNat.toFinEncoding)
    (PlanarHom.ConstantMachines.computer BitEncoding.unaryNat e a)
  let prepared:=transportOutputComputer BitEncoding.unaryNat (BitEncoding.unaryNat.prod e)
    (seedEncoding e a) (fun _=>rfl) prepare
  let loop:=computerOn (seedEncoding e a) e f id (fun _=>a) (fun _=>rfl) body p
    (fun n i hi=>(sizeBound n i hi).trans (natPolynomial_monotone p (by
      simp only [seedEncoding,BitEncoding.retract,BitEncoding.prod_length,BitEncoding.unaryNat_length]
      omega)))
  exact composeComputers prepared loop

end PlanarHom.BoundedIterationMachine
