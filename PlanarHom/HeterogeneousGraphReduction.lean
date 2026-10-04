import PlanarHom.GraphNonadaptiveReduction
namespace PlanarHom.Complexity.MixedCode
noncomputable section
open Turing PlanarHom.MachineComposition
variable {C D K : Type} [Fintype C] [Fintype D] [Field K] [Algebra ℚ K]
variable {dimension bt ut bs us : ℕ}
private def rawView (H : MixedCode→Prop) (raw : Bits)
    (h : ∃g,encoding.decode raw=some g ∧ H g) : BitEncoding.ValidWord encoding:=
  ⟨raw,by obtain ⟨g,hd,_⟩:=h; exact ⟨g,hd⟩⟩
private theorem rawView_property (H : MixedCode→Prop) (raw : Bits)
    (h : ∃g,encoding.decode raw=some g ∧ H g) : H (rawView H raw h).value:=by
  obtain ⟨g,hd,hg⟩:=h
  have hv : (rawView H raw ⟨g,hd,hg⟩).value=g:=BitEncoding.ValidWord.value_eq hd
  rw [hv]
  exact hg
noncomputable def reductionOfHeterogeneousPipeline {Meta : Type}
    (basis : Module.Basis (Fin dimension) ℚ K) (em : BitEncoding Meta)
    (MT : Fin bt→Matrix C C K) (UT : Fin ut→C→K) (wT : C→K)
    (MS : Fin bs→Matrix D D K) (US : Fin us→D→K) (wS : D→K)
    (HT HS : MixedCode→Prop)
    (validT : ∀g,HT g→g.Valid bt ut) (validS : ∀g,HS g→g.Valid bs us)
    (prepare : MixedCode→Meta × List MixedCode) (recover : Meta × List K→K)
    (hp : FP encoding (em.prod encoding.list) prepare)
    (hr : FP (em.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover)
    (hq : ∀g,HT g→∀query∈(prepare g).2,HS query)
    (correct : ∀g (hg : HT g),recover ((prepare g).1,(prepare g).2.map (totalEvaluation MS US wS))=
      g.evaluate (validT g hg) MT UT wT) :
    PromisePolyTimeTuringReduction (restrictedEvaluationProblem basis MT UT wT HT)
      (restrictedEvaluationProblem basis MS US wS HS):=by
  let pre:=composeComputers normalizer (Classical.choice hp)
  let post:=Classical.choice hr
  let bound:=PlanarHom.PartitionOutputBounds.exists_polynomial_raw_mixed_evaluation_length_bound basis MS US wS
  let p:=Classical.choose bound
  have hb:=Classical.choose_spec bound
  apply nonadaptiveReduction (p:=p) (BitEncoding.ValidWord.encoding encoding) em encoding
    (numberFieldEncoding basis) (numberFieldEncoding basis)
    (restrictedEvaluationProblem basis MT UT wT HT) (restrictedEvaluationProblem basis MS US wS HS)
    (prepare ∘ BitEncoding.ValidWord.value) (totalEvaluation MS US wS) recover pre post
    (rawView HT) (fun _ _=>rfl)
  · intro raw h query hquery
    have hprop:=rawView_property HT raw h
    exact ⟨query,encoding.decode_encode query,hq _ hprop query hquery⟩
  · intro query hquery
    obtain ⟨g,hd,hg⟩:=hquery
    rw [encoding.decode_encode] at hd
    have he : query=g:=Option.some.inj hd
    subst g
    change evaluationValue basis MS US wS (encoding.encode query)=
      (numberFieldEncoding basis).encode (totalEvaluation MS US wS query)
    rw [evaluationValue_encode basis MS US wS query (validS query hg),
      totalEvaluation_valid MS US wS query (validS query hg)]
  · intro raw h
    have hprop:=rawView_property HT raw h
    have hc:=correct (rawView HT raw h).value hprop
    change (numberFieldEncoding basis).encode
      (recover (prepare (rawView HT raw h).value |>.1,
        (prepare (rawView HT raw h).value).2.map (totalEvaluation MS US wS)))=
      evaluationValue basis MT UT wT raw
    rw [hc]
    exact (evaluationValue_decode basis MT UT wT raw (rawView HT raw h).value
      (BitEncoding.ValidWord.decode_raw (rawView HT raw h)) (validT _ hprop)).symm
  · intro raw h
    obtain ⟨g,hd,hg⟩:=h
    change (evaluationValue basis MS US wS raw).length≤p.eval raw.length
    rw [evaluationValue_decode basis MS US wS raw g hd (validS g hg)]
    exact hb raw g (validS g hg) hd
noncomputable def planarReductionOfHeterogeneousPipeline {Meta : Type}
    (basis : Module.Basis (Fin dimension) ℚ K) (em : BitEncoding Meta)
    (MT : Fin bt→Matrix C C K) (UT : Fin ut→C→K) (wT : C→K)
    (MS : Fin bs→Matrix D D K) (US : Fin us→D→K) (wS : D→K)
    (prepare : MixedCode→Meta × List MixedCode) (recover : Meta × List K→K)
    (hp : FP encoding (em.prod encoding.list) prepare)
    (hr : FP (em.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover)
    (hq : ∀g,g.PlanarValid bt ut→∀query∈(prepare g).2,query.PlanarValid bs us)
    (correct : ∀g (hg : g.PlanarValid bt ut),recover ((prepare g).1,(prepare g).2.map (totalEvaluation MS US wS))=
      g.evaluate hg.1 MT UT wT) :
    PromisePolyTimeTuringReduction (evaluationProblem basis MT UT wT)
      (evaluationProblem basis MS US wS):=
  reductionOfHeterogeneousPipeline basis em MT UT wT MS US wS (PlanarValid bt ut) (PlanarValid bs us)
    (fun _ h=>h.1) (fun _ h=>h.1) prepare recover hp hr hq correct
end
end PlanarHom.Complexity.MixedCode
