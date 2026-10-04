import PlanarHom.ListFoldMachines

/-! # Actual list folds on honestly encoded restricted initial states -/
namespace PlanarHom.Complexity.BitEncoding

/-- A proof restriction preserves exactly the original input word. Its decoder
checks the mathematical promise; no promise-deciding computation is claimed. -/
noncomputable def restrict {α : Type} (e : BitEncoding α) (P : α→Prop) : BitEncoding {a // P a} := by
  classical
  exact {
    encode := fun a => e.encode a.val
    decode := fun s => do
      let a ← e.decode s
      if h : P a then some ⟨a,h⟩ else none
    decode_encode := by intro a; simp [e.decode_encode,a.property] }

end PlanarHom.Complexity.BitEncoding

namespace PlanarHom.ListFoldMachines
open Turing Complexity MachineComposition
variable {α β γ : Type}

theorem foldTime_bound_local (ea : BitEncoding α) (eb : BitEncoding β) (f : β→α→β)
    (z : β) (xs : List α) (P : ℕ)
    (hacc : ∀i,i≤xs.length→(eb.encode ((xs.take i).foldl f z)).length≤P) :
    foldTime ea eb f z xs ≤
      (10*((eb.prod ea.list).encode (z,xs)).length+10)*(((eb.prod ea.list).encode (z,xs)).length+P+4) := by
  let N := ((eb.prod ea.list).encode (z,xs)).length
  have hpair : N=2*(eb.encode z).length+(ea.list.encode xs).length+1 := BitEncoding.prod_length _ _ _
  have hlist : (ea.list.encode xs).length = 2*(BitEncoding.nat.encode xs.length).length+1+
      2*(xs.map (fun a => (ea.encode a).length)).sum+xs.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hn : xs.length≤N := by omega
  have hinput (a : α) (ha : a∈xs) : (ea.encode a).length≤N := by
    have h := ListMapMachines.mem_le_sum_map (fun a => (ea.encode a).length) ha
    dsimp only at h
    omega
  have hl := loopCost_bound z xs N P hinput hacc
  have hmul := Nat.mul_le_mul_right (3*N+8*P+10) hn
  have hpre : 2*(eb.encode z).length+(BitEncoding.nat.encode xs.length).length ≤ N := by omega
  change 2*(eb.encode z).length+(BitEncoding.nat.encode xs.length).length+3+loopCost ea eb f z xs ≤ (10*N+10)*(N+P+4)
  calc
    _ ≤ N+3+(N*(3*N+8*P+10)+2*P+3) := by omega
    _ ≤ _ := by nlinarith

/-- Reuse the actual fold machine when its accumulator/list codeword is present
literally. Prefix bounds are demanded only for the supplied reachable starts. -/
noncomputable def computerOn (input : BitEncoding γ) (ea : BitEncoding α) (eb : BitEncoding β)
    (f : β→α→β) (start : γ→β) (items : γ→List α)
    (sameWords : ∀b,input.encode b=(eb.prod ea.list).encode (start b,items b))
    (body : TM2ComputableInPolyTime (eb.prod ea).toFinEncoding eb.toFinEncoding (fun p => f p.1 p.2))
    (p : Polynomial ℕ)
    (sizeBound : ∀b i,i≤(items b).length→(eb.encode (((items b).take i).foldl f (start b))).length≤
      p.eval (input.encode b).length) :
    TM2ComputableInPolyTime input.toFinEncoding eb.toFinEncoding (fun b => (items b).foldl f (start b)) := by
  let time : Polynomial ℕ := (Polynomial.C 10*Polynomial.X+Polynomial.C 10)*(Polynomial.X+p+Polynomial.C 4)
  let g := body.toTM2ComputableAux
  refine {
    tm := OracleSubstitution.machine machine g
    inputAlphabet := machine.core.inputAlphabet
    outputAlphabet := machine.core.outputAlphabet
    time := OracleSubstitution.timePolynomial machine time body.time
    outputsFun := ?_ }
  intro b
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost,hgood⟩ := run (ea:=ea) (eb:=eb) (f:=f) (start b) (items b)
  rw [←sameWords b] at hr
  have hN : ∀k,((machine.initial (input.encode b)).stk k).length≤(input.encode b).length :=
    OracleReductionComposition.initial_length machine _
  have hc : cost≤time.eval (input.encode b).length := by
    apply hcost.trans
    have h := foldTime_bound_local ea eb f (start b) (items b) (p.eval (input.encode b).length) (sizeBound b)
    simpa only [time,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,←sameWords b] using h
  obtain ⟨t,ht,he⟩ := OracleSubstitution.compiled_run_on_trace machine g hr body.time
    (fun q a hqa => by
      apply Classical.choice
      obtain ⟨x,hx⟩ := hgood (q,a) hqa
      have hq := congrArg Prod.fst hx
      have ha := congrArg Prod.snd hx
      dsimp only at hq ha
      subst q; subst a
      exact ⟨body.outputsFun x⟩) _ hN
  refine ⟨{steps:=t,evals_in_steps:=?_,steps_le_m:=?_}⟩
  · rw [OracleSubstitution.idle_initial,OracleSubstitution.idle_final] at he
    exact he
  · exact ht.trans (OracleReductionComposition.bound_polynomial machine time body.time
      (input.encode b).length cost hc)

end PlanarHom.ListFoldMachines
