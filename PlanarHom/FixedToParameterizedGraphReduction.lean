import PlanarHom.ParameterizedGraphReduction
import PlanarHom.GraphNonadaptiveReduction

/-! NEW raw graph to parameterized graph pipeline compiler. The source's actual
simulator supplies the charged oracle-answer bound; all raw successful graph
encodings and the ordinary topological planar promise are retained. -/
noncomputable section
namespace PlanarHom.FixedToParameterizedGraphReduction
open Complexity Complexity.MixedCode MachineComposition
variable {C X Meta K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension q bt ut bs us : ℕ}

private def rawView (raw : Bits) (h : PlanarInput bt ut raw) : BitEncoding.ValidWord encoding:=
  ⟨raw,by obtain ⟨g,hd,_⟩:=h;exact ⟨g,hd⟩⟩
private theorem rawView_property (raw : Bits) (h : PlanarInput bt ut raw) :
    (rawView raw h).value.PlanarValid bt ut:=by
  obtain ⟨g,hd,hg⟩:=h
  have hv:(rawView raw ⟨g,hd,hg⟩).value=g:=BitEncoding.ValidWord.value_eq hd
  rw [hv]
  exact hg

def reductionOfPipeline
    (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X) (em : BitEncoding Meta)
    (MT : Fin bt→Matrix C C K) (UT : Fin ut→C→K) (wT : C→K)
    (MS : Fin bs→Matrix (Fin q) (Fin q) K) (US : Fin us→Fin q→K) (wS : Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (prepare : MixedCode→Meta×List (X×MixedCode)) (recover : Meta×List K→K)
    (hp : FP encoding (em.prod (ex.prod encoding).list) prepare)
    (hr : FP (em.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover)
    (hq : ∀g,g.PlanarValid bt ut→∀query∈(prepare g).2,
      allowed query.1 ∧ query.2.PlanarValid (bs+1) us)
    (correct : ∀g (hg:g.PlanarValid bt ut),
      recover ((prepare g).1,(prepare g).2.map (ParameterizedMatrixEvaluation.answer MS US wS F))=
        g.evaluate hg.1 MT UT wT)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex MS US wS F allowed) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis MT UT wT)
      (ParameterizedMatrixEvaluation.problem basis ex MS US wS F allowed) := by
  let target:=evaluationProblem basis MT UT wT
  let source:=ParameterizedMatrixEvaluation.problem basis ex MS US wS F allowed
  let pre:=composeComputers normalizer (Classical.choice hp)
  apply nonadaptiveReduction (p:=simulation.outputPolynomial) (BitEncoding.ValidWord.encoding encoding)
    em (ex.prod encoding) (numberFieldEncoding basis) (numberFieldEncoding basis) target source
    (prepare ∘ BitEncoding.ValidWord.value) (ParameterizedMatrixEvaluation.answer MS US wS F) recover pre
    (Classical.choice hr) rawView (fun _ _=>rfl)
  · intro raw h query hquery
    have hh:=hq _ (rawView_property raw h) query hquery
    exact ⟨ParameterizedGraphReduction.canonicalView query,
      ParameterizedGraphReduction.canonicalView_encode ex query,hh.1,
      by simpa only [ParameterizedGraphReduction.canonicalView_value] using hh.2⟩
  · intro query _
    exact ParameterizedGraphReduction.value_encode basis ex MS US wS F allowed query
  · intro raw h
    have hh:=correct (rawView raw h).value (rawView_property raw h)
    change (numberFieldEncoding basis).encode (recover _)=evaluationValue basis MT UT wT raw
    dsimp only [Function.comp_def]
    rw [hh]
    exact (evaluationValue_decode basis MT UT wT raw (rawView raw h).value
      (BitEncoding.ValidWord.decode_raw (rawView raw h)) (rawView_property raw h).1).symm
  · exact simulation.output_length_bound

end PlanarHom.FixedToParameterizedGraphReduction
