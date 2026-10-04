import PlanarHom.OracleSubstitution

/-! Oracle substitution only requires correctness on the actual query transcript.
This permits typed subroutines on canonical codewords without assuming that their
machines halt or normalize malformed raw inputs. -/
namespace PlanarHom.OracleSubstitution
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.MachineComposition

variable (m : OracleTM2) (g : TM2ComputableAux Bool Bool)

/-- A strengthened simulation invariant, charging all query/answer communication
and requiring callee correctness only for recorded query-answer pairs. -/
theorem compiled_run_on_trace_uniform {oracle : Bits→Bits}
    {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : m.Run oracle c d steps cost qs) (p : Polynomial ℕ)
    (outputs : ∀q a,(q,a)∈qs→TM2OutputsInTime g.tm (q.map g.inputAlphabet.symm)
      (some (a.map g.outputAlphabet.symm)) (p.eval q.length))
    (C L N : ℕ) (hN : ∀k,(c.stk k).length≤N) (hcost : cost≤C)
    (hspace : N+(machinePushBound m.core.tm+1)*cost≤L) :
    ∃n,n≤steps*(6+L+4*C+p.eval C) ∧
      iter m g n (idle m.core.tm g.tm c)=some (idle m.core.tm g.tm d):=by
  induction hr generalizing N with
  | refl c=>exact ⟨0,by simp,rfl⟩
  | @ordinary c d e steps cost qs hn ht hr ih=>
    have hN' : ∀k,(d.stk k).length≤N+machinePushBound m.core.tm:=
      step_length_le m.core.tm ht N hN
    have hcost' : cost≤C:=by omega
    have hspace' : N+machinePushBound m.core.tm+(machinePushBound m.core.tm+1)*cost≤L:=by
      simp only [Nat.mul_add,Nat.mul_one] at hspace
      omega
    obtain ⟨n,hbound,hrun⟩:=ih outputs (N+machinePushBound m.core.tm) hN' hcost' hspace'
    refine ⟨n+1,?_,?_⟩
    · rw [Nat.add_mul,Nat.one_mul]; omega
    · rw [iter,Function.iterate_succ_apply]
      change (fun x : Option (machine m g).Cfg=>x.bind (machine m g).step)^[n]
        ((machine m g).step (idle m.core.tm g.tm c))=_
      rw [ordinary_step m g c d hn ht]
      exact hrun
  | @query c e steps cost qs next hq hr ih=>
    have hN' : ∀k,((m.answerCfg oracle c next).stk k).length≤N+(oracle (m.queryWord c)).length:=by
      intro k
      by_cases hk:k=m.answerStack
      · subst k
        simp only [OracleTM2.answerCfg,Function.update_self,List.length_map]
        omega
      · simpa [OracleTM2.answerCfg,Function.update_of_ne hk] using
          (hN k).trans (Nat.le_add_right N (oracle (m.queryWord c)).length)
    have hcost' : cost≤C:=by omega
    have hspace' : N+(oracle (m.queryWord c)).length+(machinePushBound m.core.tm+1)*cost≤L:=by
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at hspace ⊢
      omega
    obtain ⟨n,hbound,hrun⟩:=ih (fun q a ha=>outputs q a (List.mem_cons_of_mem _ ha))
      (N+(oracle (m.queryWord c)).length) hN' hcost' hspace'
    let out:=outputs (m.queryWord c) (oracle (m.queryWord c)) (by simp)
    have hquery:=query_run_exact m g oracle c next hq (p.eval (m.queryWord c).length) out
    have hqcost : (m.queryWord c).length≤C:=by omega
    have hacost : (oracle (m.queryWord c)).length≤C:=by omega
    have hpoly : p.eval (m.queryWord c).length≤p.eval C:=natPolynomial_monotone p hqcost
    have hanswer : (c.stk m.answerStack).length≤L:=by
      have ha:=hN m.answerStack
      omega
    have htbound : 6+(c.stk m.answerStack).length+2*(m.queryWord c).length+
        2*(oracle (m.queryWord c)).length+out.steps≤6+L+4*C+p.eval C:=by
      have ho:=out.steps_le_m
      omega
    refine ⟨n+(6+(c.stk m.answerStack).length+2*(m.queryWord c).length+
      2*(oracle (m.queryWord c)).length+out.steps),?_,?_⟩
    · rw [Nat.add_mul,Nat.one_mul]
      exact Nat.add_le_add hbound htbound
    · unfold iter at hquery hrun ⊢
      rw [Function.iterate_add_apply,hquery,hrun]

/-- Actual ordinary-machine simulation with the same cumulative polynomial
bound as unrestricted substitution, but no behavior demanded off the trace. -/
theorem compiled_run_on_trace {oracle : Bits→Bits}
    {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : m.Run oracle c d steps cost qs) (p : Polynomial ℕ)
    (outputs : ∀q a,(q,a)∈qs→TM2OutputsInTime g.tm (q.map g.inputAlphabet.symm)
      (some (a.map g.outputAlphabet.symm)) (p.eval q.length))
    (N : ℕ) (hN : ∀k,(c.stk k).length≤N) :
    ∃n,n≤cost*(6+N+(machinePushBound m.core.tm+5)*cost+p.eval cost) ∧
      iter m g n (idle m.core.tm g.tm c)=some (idle m.core.tm g.tm d):=by
  obtain ⟨n,hn,hrun⟩:=compiled_run_on_trace_uniform m g hr p outputs cost
    (N+(machinePushBound m.core.tm+1)*cost) N hN (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨n,?_,hrun⟩
  have hb:=hn.trans (Nat.mul_le_mul_right _ hr.steps_le)
  have heq : 6+(N+(machinePushBound m.core.tm+1)*cost)+4*cost+p.eval cost=
      6+N+(machinePushBound m.core.tm+5)*cost+p.eval cost:=by
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  rw [heq] at hb
  exact hb

end PlanarHom.OracleSubstitution
