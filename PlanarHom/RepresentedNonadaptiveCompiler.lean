import PlanarHom.RepresentedBatchBounds
import PlanarHom.NonadaptiveReductionCompiler

/-! Genuine represented-output nonadaptive reduction compilation. Arbitrary
valid oracle representatives are accepted and their complete literal byte
volume is charged; query count and query sizes depend only on input length.
No field codec, canonical answer, or oracle answer-length bound is assumed. -/
noncomputable section
namespace PlanarHom.RepresentedBit
open Complexity Turing Polynomial PlanarHom.MachineComposition

 def compileNonadaptive {A C Q R:Type}
    (ea:BitEncoding A) (ec:BitEncoding C) (eq:BitEncoding Q) (er:BitEncoding R)
    (target source:Problem) (prepare:A→C×List Q) (recover:R→Bits)
    (preprocessing:TM2ComputableInPolyTime ea.toFinEncoding (ec.prod eq.list).toFinEncoding prepare)
    (recovery:TM2ComputableInPolyTime er.toFinEncoding BitEncoding.bits.toFinEncoding recover)
    (view:∀raw,target.valid raw→A)
    (sameWords:∀raw h,ea.encode (view raw h)=raw)
    (queriesValid:∀raw h,∀q∈(prepare (view raw h)).2,source.valid (eq.encode q))
    (postView:∀raw h (answers:Q→Bits),
      (∀q∈(prepare (view raw h)).2,source.answer (eq.encode q) (answers q))→R)
    (postWords:∀raw h answers ha,er.encode (postView raw h answers ha)=
      (ec.prod BitEncoding.bits.list).encode ((prepare (view raw h)).1,(prepare (view raw h)).2.map answers))
    (recoveryCorrect:∀raw h answers ha,target.answer raw (recover (postView raw h answers ha))) :
    Reduction target source := by
  let pre:=FiniteReachableAlphabetMachines.restrictComputer preprocessing
  let post:=FiniteReachableAlphabetMachines.restrictComputer recovery
  letI:∀k,Fintype (pre.tm.Γ k):=FiniteReachableAlphabetMachines.alphabetFintype preprocessing
  letI:∀k,Fintype (post.tm.Γ k):=FiniteReachableAlphabetMachines.alphabetFintype recovery
  let batch:=ContextualOracleBatch.machine
  let first:=OraclePrecomposition.machine pre.toTM2ComputableAux batch
  let final:=OraclePostcomposition.machine first post.toTM2ComputableAux
  let P:=outputLengthPolynomial pre
  let mid:=P+Polynomial.C 2*X
  let work:=pre.time+Polynomial.C 20*(P+X+Polynomial.C 1)+post.time.comp mid
  refine ⟨final,work,P,P,?_⟩
  intro oracle ho raw hvalid
  let a:=view raw hvalid
  let context:=(prepare a).1
  let queries:=(prepare a).2
  let words:=queries.map eq.encode
  let prepared:=(ec.prod eq.list).encode (prepare a)
  let answers:Q→Bits:=fun q=>oracle (eq.encode q)
  let recoveredInput:=(ec.prod BitEncoding.bits.list).encode (context,queries.map answers)
  have ha:∀q∈queries,source.answer (eq.encode q) (answers q):=
    fun q hq=>ho _ (queriesValid raw hvalid q hq)
  let postInput:=postView raw hvalid answers ha
  let result:=recover postInput
  have hpostWords:er.encode postInput=recoveredInput:=postWords raw hvalid answers ha
  have hraw:ea.encode a=raw:=sameWords raw hvalid
  have hprepare:prepared=(BitEncoding.bits.prod BitEncoding.bits.list).encode (ec.encode context,words) := by
    change BitEncoding.frame (ec.encode context)++eq.list.encode queries=
      BitEncoding.frame (ec.encode context)++BitEncoding.bits.list.encode (queries.map eq.encode)
    rw [BitEncoding.list_codewords]
  have hmid:recoveredInput=(BitEncoding.bits.prod BitEncoding.bits.list).encode
      (ec.encode context,words.map oracle) := by
    simp only [recoveredInput,words,answers,List.map_map,Function.comp_def,BitEncoding.prod,BitEncoding.bits,id_eq]
  obtain ⟨steps,cost,hr,hcost⟩:=RepresentedListBatch.contextual_run oracle (ec.encode context) words
  rw [←hprepare,←hmid] at hr
  rw [←hprepare] at hcost
  let trace:=RepresentedListBatch.transcript oracle words
  change cost≤20*(prepared.length+replyVolume trace+1) at hcost
  have hpre:TM2OutputsInTime pre.tm (raw.map pre.inputAlphabet.symm)
      (some (prepared.map pre.outputAlphabet.symm)) (pre.time.eval raw.length) := by
    simpa only [BitEncoding.toFinEncoding,hraw,prepared] using pre.outputsFun a
  have hpost:TM2OutputsInTime post.tm (recoveredInput.map post.inputAlphabet.symm)
      (some (result.map post.outputAlphabet.symm)) (post.time.eval recoveredInput.length) := by
    have h:=post.outputsFun postInput
    simpa only [BitEncoding.toFinEncoding,hpostWords,BitEncoding.bits,id_eq] using h
  have hfirst:=OraclePrecomposition.run pre.toTM2ComputableAux batch raw prepared recoveredInput _ hpre hr
  have hfinal:=OraclePostcomposition.run first post.toTM2ComputableAux raw recoveredInput result hfirst _ hpost
  have hcorrect:target.answer raw result := recoveryCorrect raw hvalid answers ha
  have hpreSize:prepared.length≤P.eval raw.length := by
    simpa only [BitEncoding.toFinEncoding,hraw,prepared,P] using encoded_output_length_le pre a
  have hlistSize:(BitEncoding.bits.list.encode words).length≤prepared.length := by
    rw [hprepare]
    simp only [BitEncoding.prod_length,BitEncoding.bits,id_eq]
    omega
  have hmidSize:recoveredInput.length≤prepared.length+2*replyVolume trace := by
    rw [hprepare,hmid]
    exact RepresentedListBatch.contextual_output_length_le oracle (ec.encode context) words
  refine ⟨result,_,_,trace,hfinal,hcorrect,?_,?_,?_,?_⟩
  · intro q answer hq
    obtain ⟨word,hw,heq⟩:=List.mem_map.mp hq
    have heq':word=q:=congrArg Prod.fst heq
    subst word
    obtain ⟨item,hi,rfl⟩:=List.mem_map.mp hw
    exact queriesValid raw hvalid item hi
  · change (words.map (fun q=>(q,oracle q))).length≤P.eval raw.length
    rw [List.length_map]
    exact (RepresentedListBatch.query_count_le_input words).trans (hlistSize.trans hpreSize)
  · intro q answer hq
    obtain ⟨word,hw,heq⟩:=List.mem_map.mp hq
    have heq':word=q:=congrArg Prod.fst heq
    subst word
    exact (RepresentedListBatch.query_length_le_input words q hw).trans (hlistSize.trans hpreSize)
  · have hN:raw.length≤raw.length+replyVolume trace:=Nat.le_add_right _ _
    have hP:prepared.length≤P.eval (raw.length+replyVolume trace):=
      hpreSize.trans (natPolynomial_monotone P hN)
    have hc:cost≤20*(P.eval (raw.length+replyVolume trace)+(raw.length+replyVolume trace)+1) := by
      omega
    have hm:recoveredInput.length≤mid.eval (raw.length+replyVolume trace) := by
      simp only [mid,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      omega
    have hp: hpre.steps≤pre.time.eval (raw.length+replyVolume trace):=
      hpre.steps_le_m.trans (natPolynomial_monotone pre.time hN)
    have hq: hpost.steps≤post.time.eval (mid.eval (raw.length+replyVolume trace)):=
      hpost.steps_le_m.trans (natPolynomial_monotone post.time hm)
    simp only [work,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_comp]
    omega

end PlanarHom.RepresentedBit
