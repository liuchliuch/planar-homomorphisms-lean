import PlanarHom.RepresentedBitModel

/-! Actual solver substitution for arbitrary represented answers. The oracle
program is uniform and correct for all semantic representatives, even oversized
ones. For a polynomial-time solver its real output-length polynomial bounds
reply volume, and the existing charged TM2 substitution compiler is reused. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity Turing PlanarHom.MachineComposition

/-- Evaluate the work budget after charging polynomially many replies, each
bounded by the actual solver's output-length polynomial at the query bound. -/
def Reduction.solverCost {P Q:Problem} (r:Reduction P Q) (answerBound:Polynomial ℕ) : Polynomial ℕ :=
  r.work.comp (Polynomial.X+r.queryCount*(answerBound.comp r.querySize))

/-- No preferred representative is part of the reduction contract. Selecting
an actual solver here is precisely ordinary oracle elimination. -/
theorem Reduction.inFP {P Q:Problem} (r:Reduction P Q) (hq:Q.InFP) : P.InFP := by
  obtain ⟨f,hfp,hcorrect⟩:=hq
  let solver:=Classical.choice hfp
  let oracle:Bits→Bits:=fun x=>if hx:Q.valid x then f ⟨x,hx⟩ else []
  have ho:∀q,Q.valid q→Q.answer q (oracle q) := by
    intro q hq
    simpa only [oracle,dif_pos hq] using hcorrect ⟨q,hq⟩
  let out:{x:Bits // P.valid x}→Bits:=fun x=>Classical.choose (r.computes oracle ho x.val x.property)
  have data (x:{x:Bits // P.valid x}) : ∃steps cost qs,
      r.machine.Run oracle (r.machine.initial x.val) (r.machine.final (out x)) steps cost qs ∧
      P.answer x.val (out x) ∧ (∀q a,(q,a)∈qs→Q.valid q) ∧
      qs.length≤r.queryCount.eval x.val.length ∧
      (∀q a,(q,a)∈qs→q.length≤r.querySize.eval x.val.length) ∧
      cost≤r.work.eval (x.val.length+replyVolume qs) :=
    Classical.choose_spec (r.computes oracle ho x.val x.property)
  refine ⟨out,?_,?_⟩
  · let g:=solver.toTM2ComputableAux
    let answerBound:=outputLengthPolynomial solver
    let cp:=r.solverCost answerBound
    refine ⟨{
      tm:=OracleSubstitution.machine r.machine g
      inputAlphabet:=r.machine.core.inputAlphabet
      outputAlphabet:=r.machine.core.outputAlphabet
      time:=OracleSubstitution.timePolynomial r.machine cp solver.time
      outputsFun:=?_ }⟩
    intro x
    apply Classical.choice
    obtain ⟨steps,cost,qs,hr,hout,hvalid,hcount,hsize,hwork⟩:=data x
    have hanswer:∀q a,(q,a)∈qs→a.length≤answerBound.eval q.length := by
      intro q a hqa
      have ha:=PromisedFPClosureReconstruction.transcript_answer hr q a hqa
      have hv:=hvalid q a hqa
      rw [ha]
      have hlen:=encoded_output_length_le solver ⟨q,hv⟩
      simpa only [oracle,dif_pos hv,BitEncoding.bits,BitEncoding.restrict] using hlen
    have hvol:replyVolume qs≤r.queryCount.eval x.val.length*
        answerBound.eval (r.querySize.eval x.val.length) := by
      have hh:=replyVolume_le qs (answerBound.eval (r.querySize.eval x.val.length)) (by
        intro q a hqa
        exact (hanswer q a hqa).trans (natPolynomial_monotone answerBound (hsize q a hqa)))
      exact hh.trans (Nat.mul_le_mul_right _ hcount)
    have hcost:cost≤cp.eval x.val.length := by
      have hh:=hwork.trans (natPolynomial_monotone r.work (Nat.add_le_add_left hvol _))
      simpa only [cp,Reduction.solverCost,Polynomial.eval_comp,Polynomial.eval_add,
        Polynomial.eval_mul,Polynomial.eval_X] using hh
    have hN:∀k,((r.machine.initial x.val).stk k).length≤x.val.length :=
      OracleReductionComposition.initial_length r.machine x.val
    obtain ⟨n,hn,he⟩:=OracleSubstitution.compiled_run_on_trace r.machine g hr solver.time
      (fun q a hqa=>by
        have ha:=PromisedFPClosureReconstruction.transcript_answer hr q a hqa
        have hv:=hvalid q a hqa
        rw [ha]
        simpa only [oracle,dif_pos hv] using solver.outputsFun ⟨q,hv⟩) x.val.length hN
    refine ⟨{steps:=n,evals_in_steps:=?_,steps_le_m:=?_}⟩
    · rw [OracleSubstitution.idle_initial,OracleSubstitution.idle_final] at he
      exact he
    · exact hn.trans (OracleReductionComposition.bound_polynomial r.machine cp solver.time
        x.val.length cost hcost)
  · intro x
    obtain ⟨steps,cost,qs,hr,hout,hrest⟩:=data x
    exact hout

end PlanarHom.RepresentedBit
