import PlanarHom.ContextualOracleBatch
import PlanarHom.OracleOutputAccounting

/-! All-valid-extension promise reduction for batches retaining exact metadata. -/
namespace PlanarHom.Complexity
open Polynomial PlanarHom.MachineComposition

def contextualBatchProblem (P : PromiseProblem) : PromiseProblem where
  valid input:=∃context : Bits,∃qs : List Bits,
    input=(BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs) ∧ ∀q∈qs,P.valid q
  value:=encodedFunction (BitEncoding.bits.prod BitEncoding.bits.list)
    (BitEncoding.bits.prod BitEncoding.bits.list) (fun p=>(p.1,p.2.map P.value)) []

noncomputable def contextualBatchTime (p : Polynomial ℕ) : Polynomial ℕ:=
  (C 4*X+C 4)*(X+p+C 4)+C 3*X+C 4

noncomputable def contextualBatchReduction (P : PromiseProblem) (p : Polynomial ℕ)
    (bound : ∀q,P.valid q→(P.value q).length≤p.eval q.length) :
    PromisePolyTimeTuringReduction (contextualBatchProblem P) P where
  machine:=PlanarHom.ContextualOracleBatch.machine
  time:=contextualBatchTime p
  computes oracle ho input hi:=by
    obtain ⟨context,qs,rfl,hvalid⟩:=hi
    obtain ⟨steps,cost,trace,hr,hcost,hgood⟩:=(batchReduction P p bound).computes oracle ho
      (BitEncoding.bits.list.encode qs) ⟨qs,rfl,hvalid⟩
    have hv : (batchProblem P).value (BitEncoding.bits.list.encode qs)=
        BitEncoding.bits.list.encode (qs.map P.value):=encodedFunction_encode _ _ _ _ _
    rw [hv] at hr
    have h:=PlanarHom.ContextualOracleBatch.run context (BitEncoding.bits.list.encode qs)
      (BitEncoding.bits.list.encode (qs.map P.value)) hr
    refine ⟨context.length+1+steps+((BitEncoding.frame context).length+2),
      context.length+1+cost+((BitEncoding.frame context).length+2),trace,?_,?_,hgood⟩
    · have hvCtx : (contextualBatchProblem P).value
          ((BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs))=
          (BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs.map P.value):=
        encodedFunction_encode _ _ _ _ _
      rw [hvCtx]
      exact h
    · let N:=((BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs)).length
      have hN : N=2*context.length+1+(BitEncoding.bits.list.encode qs).length:=by
        simp only [N,BitEncoding.prod_length,BitEncoding.bits,id_eq]
        omega
      have hq : (BitEncoding.bits.list.encode qs).length≤N:=by omega
      have hc : context.length≤N:=by omega
      have hm:=natPolynomial_monotone ((batchReduction P p bound).time) hq
      have hcost':cost≤((C 4*X+C 4)*(X+p+C 4)).eval N:=hcost.trans hm
      simp only [contextualBatchTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
        Polynomial.eval_X,BitEncoding.frame_length]
      change _≤(4*N+4)*(N+p.eval N+4)+3*N+4
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at hcost'
      omega

/-- The actual caller's output is polynomially bounded by charged execution,
including copied oracle answers and retained context bytes. -/
noncomputable def contextualBatchOutputTime (p : Polynomial ℕ) : Polynomial ℕ:=
  X+C (machinePushBound PlanarHom.ContextualOracleBatch.machine.core.tm+1)*contextualBatchTime p

end PlanarHom.Complexity
