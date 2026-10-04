import PlanarHom.RepresentedNestedRunAccounting
import PlanarHom.RepresentedBitModel
import PlanarHom.OracleOutputAccounting
import PlanarHom.PromisedFPReductionClosure
import PlanarHom.ListMapMachines

/-! Actual oracle-to-oracle composition for represented answers. Intermediate
answers are produced by the inner machine, and their lengths are bounded by
its charged output growth. No bounded-size or canonical representative oracle
is imposed at either interface. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity MachineComposition

private structure Execution {P Q:Problem} (r:Reduction P Q) (oracle:Bits → Bits) (x:Bits) where
  output : Bits
  steps : ℕ
  cost : ℕ
  trace : OracleTM2.Transcript
  run : r.machine.Run oracle (r.machine.initial x) (r.machine.final output) steps cost trace
  answer : P.answer x output
  valid : ∀q a,(q,a)∈trace → Q.valid q
  count : trace.length≤r.queryCount.eval x.length
  size : ∀q a,(q,a)∈trace → q.length≤r.querySize.eval x.length
  work : cost≤r.work.eval (x.length+replyVolume trace)

private def execution {P Q:Problem} (r:Reduction P Q) (oracle:Bits → Bits)
    (ho:∀q,Q.valid q → Q.answer q (oracle q)) (x:Bits) (hx:P.valid x) : Execution r oracle x :=
  Classical.choose (show ∃d:Execution r oracle x,True from by
    obtain ⟨y,s,c,qs,hr,ha,hv,hn,hs,hw⟩:=r.computes oracle ho x hx
    exact ⟨⟨y,s,c,qs,hr,ha,hv,hn,hs,hw⟩,trivial⟩)

theorem replyVolume_append (xs ys:OracleTM2.Transcript) :
    replyVolume (xs++ys)=replyVolume xs+replyVolume ys := by
  simp [replyVolume,List.map_append,List.sum_append]

theorem replyVolume_flatMap (xs:OracleTM2.Transcript) (f:Bits → OracleTM2.Transcript) :
    replyVolume (xs.flatMap (fun qa=>f qa.1))=(xs.map (fun qa=>replyVolume (f qa.1))).sum := by
  induction xs with
  | nil=>rfl
  | cons qa xs ih=>simp only [List.flatMap_cons,replyVolume_append,List.map_cons,List.sum_cons,ih]

theorem replyVolume_inner_le {xs:OracleTM2.Transcript} (f:Bits → OracleTM2.Transcript)
    {q a:Bits} (h:(q,a)∈xs) : replyVolume (f q)≤replyVolume (xs.flatMap (fun qa=>f qa.1)) := by
  rw [replyVolume_flatMap]
  exact ListMapMachines.mem_le_sum_map (fun qa=>replyVolume (f qa.1)) h

/-- The same actual nested oracle machine as canonical composition, with the
stronger represented-answer budgets and exact expanded transcript. -/
def Reduction.trans {P Q R:Problem} (r:Reduction P Q) (s:Reduction Q R) : Reduction P R := by
  let B:=s.work.comp (r.querySize+Polynomial.X)
  let A:=r.querySize+Polynomial.C (machinePushBound s.machine.core.tm+1)*B
  let O:=r.work.comp (Polynomial.X+r.queryCount*A)
  let T:=O*(Polynomial.C 6+Polynomial.X+Polynomial.C (machinePushBound r.machine.core.tm+5)*O+B)
  refine ⟨OracleReductionComposition.composeMachine r.machine s.machine,T,
    r.queryCount*(s.queryCount.comp r.querySize),s.querySize.comp r.querySize,?_⟩
  intro oracle ho x hx
  let inner:∀q,Q.valid q → Execution s oracle q:=fun q hq=>execution s oracle ho q hq
  let middle:Bits → Bits:=fun q=>if hq:Q.valid q then (inner q hq).output else []
  let traces:Bits → OracleTM2.Transcript:=fun q=>if hq:Q.valid q then (inner q hq).trace else []
  have hmiddle:∀q,Q.valid q → Q.answer q (middle q) := by
    intro q hq
    simpa only [middle,dif_pos hq] using (inner q hq).answer
  let out:=execution r middle hmiddle x hx
  let bigTrace:=out.trace.flatMap (fun qa=>traces qa.1)
  let N:=x.length+replyVolume bigTrace
  have hn:x.length≤N:=Nat.le_add_right _ _
  have hinnerVol:∀q a (hqa:(q,a)∈out.trace),replyVolume (inner q (out.valid q a hqa)).trace≤replyVolume bigTrace := by
    intro q a hqa
    have hv:=out.valid q a hqa
    have hh:=replyVolume_inner_le traces hqa
    simpa only [traces,dif_pos hv] using hh
  have hinnerCost:∀q a (hqa:(q,a)∈out.trace),(inner q (out.valid q a hqa)).cost≤B.eval N := by
    intro q a hqa
    have hv:=out.valid q a hqa
    have hq:q.length≤r.querySize.eval N:=(out.size q a hqa).trans (natPolynomial_monotone r.querySize hn)
    have hvol:=hinnerVol q a hqa
    have hval:replyVolume bigTrace≤N:=Nat.le_add_left _ _
    have hh: q.length+replyVolume (inner q hv).trace≤(r.querySize+Polynomial.X).eval N := by
      simp only [Polynomial.eval_add,Polynomial.eval_X]
      omega
    simpa only [B,Polynomial.eval_comp] using (inner q hv).work.trans (natPolynomial_monotone s.work hh)
  have hanswer:∀q a,(q,a)∈out.trace → a.length≤A.eval N := by
    intro q a hqa
    have hv:=out.valid q a hqa
    have he:=PromisedFPClosureReconstruction.transcript_answer out.run q a hqa
    have hh:=(inner q hv).run.output_length_bound
    have hc:=hinnerCost q a hqa
    have hq:q.length≤r.querySize.eval N:=(out.size q a hqa).trans (natPolynomial_monotone r.querySize hn)
    simp only [middle,dif_pos hv] at he
    rw [he]
    calc
      _≤q.length+(machinePushBound s.machine.core.tm+1)*(inner q hv).cost:=hh
      _≤r.querySize.eval N+(machinePushBound s.machine.core.tm+1)*B.eval N:=
        Nat.add_le_add hq (Nat.mul_le_mul_left _ hc)
      _=A.eval N:=by simp only [A,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  have hvol:replyVolume out.trace≤r.queryCount.eval N*A.eval N := by
    have hh:=replyVolume_le out.trace (A.eval N) hanswer
    exact hh.trans (Nat.mul_le_mul_right _ (out.count.trans (natPolynomial_monotone r.queryCount hn)))
  have hcost:out.cost≤O.eval N := by
    have hh:x.length+replyVolume out.trace≤(Polynomial.X+r.queryCount*A).eval N := by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X]
      omega
    simpa only [O,Polynomial.eval_comp] using out.work.trans (natPolynomial_monotone r.work hh)
  let V:Bits → Prop:=fun q=>∃a,(q,a)∈out.trace
  have hcallee:∀q,V q → ∃ss tt,s.machine.Run oracle (s.machine.initial q) (s.machine.final (middle q))
      ss tt (traces q) ∧ tt≤(Polynomial.C (B.eval N)).eval q.length ∧
      ∀q' a',(q',a')∈traces q → R.valid q' := by
    intro q hq
    obtain ⟨a,hqa⟩:=hq
    have hv:=out.valid q a hqa
    refine ⟨(inner q hv).steps,(inner q hv).cost,?_,
      by simpa only [Polynomial.eval_C] using hinnerCost q a hqa,?_⟩
    · simpa only [middle,traces,dif_pos hv] using (inner q hv).run
    · simpa only [traces,dif_pos hv] using (inner q hv).valid
  obtain ⟨ss,tt,hrun,ht,hvalid⟩:=out.run.replacement_run_exact (Polynomial.C (B.eval N))
    (OracleReductionComposition.composeMachine r.machine s.machine) oracle
    (OracleSubstitution.idle r.machine.core.tm s.machine.core.tm) V R.valid traces
    (OracleReductionComposition.ordinary_run r.machine s.machine oracle) (by
      intro c next hq hv
      obtain ⟨ss,tt,hrun,hbound,hlegal⟩:=hcallee (r.machine.queryWord c) hv
      exact ⟨_,_,OracleReductionComposition.query_protocol r.machine s.machine oracle middle c next hq hrun,
        Nat.add_le_add_left hbound _,hlegal⟩)
    x.length (OracleReductionComposition.initial_length r.machine x) (fun q a hqa=>⟨a,hqa⟩)
  rw [OracleReductionComposition.initial_eq,OracleReductionComposition.final_eq] at hrun
  refine ⟨out.output,ss,tt,bigTrace,hrun,out.answer,hvalid,?_,?_,?_⟩
  · have heach:∀qa∈out.trace,(traces qa.1).length≤s.queryCount.eval (r.querySize.eval x.length) := by
      rintro ⟨q,a⟩ hqa
      have hv:=out.valid q a hqa
      simp only [traces,dif_pos hv]
      exact (inner q hv).count.trans (natPolynomial_monotone s.queryCount (out.size q a hqa))
    have hh:=ListMapMachines.sum_map_le_mul (fun qa=>(traces qa.1).length) out.trace _ heach
    have hsize:=hh.trans (Nat.mul_le_mul_right _ out.count)
    simpa only [bigTrace,List.length_flatMap,Polynomial.eval_mul,Polynomial.eval_comp] using hsize
  · intro q a hqa
    obtain ⟨qa,houter,hinner⟩:=List.mem_flatMap.mp hqa
    have hv:=out.valid qa.1 qa.2 houter
    simp only [traces,dif_pos hv] at hinner
    simpa only [Polynomial.eval_comp] using ((inner qa.1 hv).size q a hinner).trans
      (natPolynomial_monotone s.querySize (out.size qa.1 qa.2 houter))
  · simp only [Polynomial.eval_C] at ht
    have hle:6+x.length+(machinePushBound r.machine.core.tm+5)*out.cost+B.eval N≤
        6+N+(machinePushBound r.machine.core.tm+5)*O.eval N+B.eval N :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hn _)
        (Nat.mul_le_mul_left _ hcost)) _
    have hh:=ht.trans (Nat.mul_le_mul hcost hle)
    simpa only [T,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,N] using hh

end PlanarHom.RepresentedBit
