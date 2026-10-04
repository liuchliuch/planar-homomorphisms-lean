import PlanarHom.ContextualBatchReduction
import PlanarHom.OraclePostcomposition
import PlanarHom.FiniteReachableAlphabetMachines

/-! A complete finite-oracle caller compiler: actual ordinary preprocessing,
context-preserving batch queries, then actual ordinary recovery. All input/output
words and cumulative polynomial costs are accounted for under full promises. -/
namespace PlanarHom.Complexity.BitEncoding

theorem list_codewords {α : Type} (e : BitEncoding α) (xs : List α) :
    bits.list.encode (xs.map e.encode)=e.list.encode xs:=by
  simp only [list,bits,List.length_map,List.map_map,Function.comp_def,id_eq]

end PlanarHom.Complexity.BitEncoding

namespace PlanarHom.Complexity
open Turing Polynomial PlanarHom.MachineComposition

/-- Real nonadaptive oracle reduction compilation. The codeword view describes
which original raw inputs are accepted; it is not a runtime decoding primitive.
Preprocessing and recovery are genuine typed TM2 witnesses, not operation-cost
hypotheses. Source queries may be noncanonical provided their promise holds. -/
noncomputable def nonadaptiveReduction
    {A C Q B R : Type} (ea : BitEncoding A) (ec : BitEncoding C)
    (eq : BitEncoding Q) (eb : BitEncoding B) (er : BitEncoding R)
    (target source : PromiseProblem) (prepare : A→C × List Q) (answer : Q→B) (recover : C × List B→R)
    (preprocessing : TM2ComputableInPolyTime ea.toFinEncoding (ec.prod eq.list).toFinEncoding prepare)
    (recovery : TM2ComputableInPolyTime (ec.prod eb.list).toFinEncoding er.toFinEncoding recover)
    (view : ∀raw,target.valid raw→A)
    (sameWords : ∀raw h,ea.encode (view raw h)=raw)
    (queriesValid : ∀raw h,∀q∈(prepare (view raw h)).2,source.valid (eq.encode q))
    (answerCorrect : ∀q,source.valid (eq.encode q)→source.value (eq.encode q)=eb.encode (answer q))
    (recoveryCorrect : ∀raw h,er.encode (recover ((prepare (view raw h)).1,
      (prepare (view raw h)).2.map answer))=target.value raw)
    (p : Polynomial ℕ) (answerLength : ∀q,source.valid q→(source.value q).length≤p.eval q.length) :
    PromisePolyTimeTuringReduction target source:=by
  let pre:=PlanarHom.FiniteReachableAlphabetMachines.restrictComputer preprocessing
  let post:=PlanarHom.FiniteReachableAlphabetMachines.restrictComputer recovery
  letI : ∀k,Fintype (pre.tm.Γ k):=PlanarHom.FiniteReachableAlphabetMachines.alphabetFintype preprocessing
  letI : ∀k,Fintype (post.tm.Γ k):=PlanarHom.FiniteReachableAlphabetMachines.alphabetFintype recovery
  let batch:=contextualBatchReduction source p answerLength
  let first:=PlanarHom.OraclePrecomposition.machine pre.toTM2ComputableAux batch.machine
  let final:=PlanarHom.OraclePostcomposition.machine first post.toTM2ComputableAux
  let P:=outputLengthPolynomial pre
  let T:=pre.time+(contextualBatchTime p).comp P+
    post.time.comp ((contextualBatchOutputTime p).comp P)
  refine {machine:=final,time:=T,computes:=?_}
  intro oracle ho raw hvalid
  let a:=view raw hvalid
  let context:=(prepare a).1
  let queries:=(prepare a).2
  let words:=queries.map eq.encode
  let prepared:=(ec.prod eq.list).encode (prepare a)
  let recoveredInput:=(ec.prod eb.list).encode (context,queries.map answer)
  have hraw : ea.encode a=raw:=sameWords raw hvalid
  have hprepare : prepared=(BitEncoding.bits.prod BitEncoding.bits.list).encode (ec.encode context,words):=by
    change BitEncoding.frame (ec.encode context)++eq.list.encode queries=
      BitEncoding.frame (ec.encode context)++BitEncoding.bits.list.encode (queries.map eq.encode)
    rw [BitEncoding.list_codewords]
  have hqvalid : ∀q∈words,source.valid q:=by
    intro q hq
    obtain ⟨item,hitem,rfl⟩:=List.mem_map.mp hq
    exact queriesValid raw hvalid item hitem
  have hbatchvalid : (contextualBatchProblem source).valid prepared:=⟨ec.encode context,words,hprepare,hqvalid⟩
  obtain ⟨steps,cost,trace,hr,hcost,hgood⟩:=batch.computes oracle ho prepared hbatchvalid
  have hanswer : (contextualBatchProblem source).value prepared=recoveredInput:=by
    rw [hprepare]
    change encodedFunction _ _ _ _ ((BitEncoding.bits.prod BitEncoding.bits.list).encode (ec.encode context,words))=_
    rw [encodedFunction_encode]
    have hw : words.map source.value=(queries.map answer).map eb.encode:=by
      dsimp only [words]
      rw [List.map_map,List.map_map]
      apply List.map_congr_left
      intro q hq
      exact answerCorrect q (queriesValid raw hvalid q hq)
    change BitEncoding.frame (ec.encode context)++BitEncoding.bits.list.encode (words.map source.value)=
      BitEncoding.frame (ec.encode context)++eb.list.encode (queries.map answer)
    rw [hw,BitEncoding.list_codewords]
  change PlanarHom.ContextualOracleBatch.machine.Run oracle
    (PlanarHom.ContextualOracleBatch.machine.initial prepared)
    (PlanarHom.ContextualOracleBatch.machine.final ((contextualBatchProblem source).value prepared))
    steps cost trace at hr
  rw [hanswer] at hr
  have hpre : TM2OutputsInTime pre.tm (raw.map pre.inputAlphabet.symm)
      (some (prepared.map pre.outputAlphabet.symm)) (pre.time.eval raw.length):=by
    simpa only [BitEncoding.toFinEncoding,hraw,prepared] using pre.outputsFun a
  have hpost : TM2OutputsInTime post.tm (recoveredInput.map post.inputAlphabet.symm)
      (some ((er.encode (recover (context,queries.map answer))).map post.outputAlphabet.symm))
      (post.time.eval recoveredInput.length):=post.outputsFun (context,queries.map answer)
  have hfirst:=PlanarHom.OraclePrecomposition.run pre.toTM2ComputableAux batch.machine
    raw prepared recoveredInput _ hpre hr
  have hfinal:=PlanarHom.OraclePostcomposition.run first post.toTM2ComputableAux
    raw recoveredInput (er.encode (recover (context,queries.map answer))) hfirst _ hpost
  have hcorrect : er.encode (recover (context,queries.map answer))=target.value raw:=recoveryCorrect raw hvalid
  generalize hn : hpost.steps=n at hfinal
  rw [hcorrect] at hfinal
  refine ⟨_,_,trace,hfinal,?_,hgood⟩
  have hpreSize : prepared.length≤P.eval raw.length:=by
    simpa only [BitEncoding.toFinEncoding,hraw,prepared,P] using encoded_output_length_le pre a
  have hcost' : cost≤(contextualBatchTime p).eval prepared.length:=hcost
  have hcostTotal : cost≤(contextualBatchTime p).eval (P.eval raw.length):=
    hcost'.trans (natPolynomial_monotone _ hpreSize)
  have hmidSize : recoveredInput.length≤(contextualBatchOutputTime p).eval prepared.length:=by
    have hs:=hr.output_length_bound
    have hm:=Nat.mul_le_mul_left (machinePushBound PlanarHom.ContextualOracleBatch.machine.core.tm+1) hcost'
    simp only [contextualBatchOutputTime,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    omega
  have hpostBound : post.time.eval recoveredInput.length≤
      post.time.eval ((contextualBatchOutputTime p).eval (P.eval raw.length)):=
    natPolynomial_monotone _ (hmidSize.trans (natPolynomial_monotone _ hpreSize))
  have hp:=hpre.steps_le_m
  have hq:=hpost.steps_le_m
  rw [hn] at hq
  simp only [T,Polynomial.eval_add,Polynomial.eval_comp]
  omega

end PlanarHom.Complexity
