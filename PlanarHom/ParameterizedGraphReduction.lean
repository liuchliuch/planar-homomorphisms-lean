import PlanarHom.ParameterizedMatrixEvaluation
import PlanarHom.NonadaptiveReductionCompiler
import PlanarHom.SourceSimulationOutputBounds

/-! Actual graph transformations between uniformly parameterized evaluation
problems, retaining canonical parameter words and every accepted raw graph word.
The source's already constructed simulator supplies the charged answer bound. -/
noncomputable section
namespace PlanarHom.ParameterizedGraphReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases MachineComposition
variable {X Y Meta K : Type} [Field K] [Algebra ℚ K]
variable {dimension q bt ut bs us : ℕ}

def canonicalView (p : X×MixedCode) : X×BitEncoding.ValidWord encoding :=
  (p.1,⟨encoding.encode p.2,⟨p.2,encoding.decode_encode p.2⟩⟩)

@[simp] theorem canonicalView_value (p : X×MixedCode) : (canonicalView p).2.value=p.2 :=
  BitEncoding.ValidWord.value_eq (encoding.decode_encode p.2)

@[simp] theorem canonicalView_encode (ex : BitEncoding X) (p : X×MixedCode) :
    (ParameterizedMatrixEvaluation.inputEncoding ex).encode (canonicalView p)=
      (ex.prod encoding).encode p := rfl

theorem value_encode (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K) (w : Fin q→K)
    (B : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) (p : X×MixedCode) :
    (ParameterizedMatrixEvaluation.problem basis ex M U w B allowed).value ((ex.prod encoding).encode p)=
      (numberFieldEncoding basis).encode (ParameterizedMatrixEvaluation.answer M U w B p) := by
  simpa only [canonicalView_encode,canonicalView_value] using
    ParameterizedMatrixEvaluation.value_raw_input basis ex M U w B allowed (canonicalView p)

def reductionOfPipeline
    (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X) (ey : BitEncoding Y)
    (em : BitEncoding Meta)
    (MT : Fin bt→Matrix (Fin q) (Fin q) K) (UT : Fin ut→Fin q→K) (wT : Fin q→K)
    (MS : Fin bs→Matrix (Fin q) (Fin q) K) (US : Fin us→Fin q→K) (wS : Fin q→K)
    (B : X→Matrix (Fin q) (Fin q) K) (F : Y→Matrix (Fin q) (Fin q) K)
    (allowedT : X→Prop) (allowedS : Y→Prop)
    (prepare : X×MixedCode→Meta×List (Y×MixedCode)) (recover : Meta×List K→K)
    (hp : FP (ex.prod encoding) (em.prod (ey.prod encoding).list) prepare)
    (hr : FP (em.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover)
    (hq : ∀p,allowedT p.1→p.2.PlanarValid (bt+1) ut→∀query∈(prepare p).2,
      allowedS query.1 ∧ query.2.PlanarValid (bs+1) us)
    (correct : ∀p,allowedT p.1→p.2.PlanarValid (bt+1) ut→
      recover ((prepare p).1,(prepare p).2.map (ParameterizedMatrixEvaluation.answer MS US wS F))=
        ParameterizedMatrixEvaluation.answer MT UT wT B p)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ey MS US wS F allowedS) base) :
    PromisePolyTimeTuringReduction (ParameterizedMatrixEvaluation.problem basis ex MT UT wT B allowedT)
      (ParameterizedMatrixEvaluation.problem basis ey MS US wS F allowedS) := by
  let target := ParameterizedMatrixEvaluation.problem basis ex MT UT wT B allowedT
  let source := ParameterizedMatrixEvaluation.problem basis ey MS US wS F allowedS
  let rawView : (raw : Bits)→target.valid raw→X×BitEncoding.ValidWord encoding := fun raw h=>Classical.choose h
  have hs : ∀raw (h : target.valid raw),
      (ParameterizedMatrixEvaluation.inputEncoding ex).encode (rawView raw h)=raw ∧
        allowedT (rawView raw h).1 ∧ (rawView raw h).2.value.PlanarValid (bt+1) ut :=
    fun _ h=>Classical.choose_spec h
  let pre := composeComputers (Classical.choice (ParameterizedMatrixEvaluation.fp_normalize ex)) (Classical.choice hp)
  apply nonadaptiveReduction (p:=simulation.outputPolynomial) (ParameterizedMatrixEvaluation.inputEncoding ex)
    em (ey.prod encoding) (numberFieldEncoding basis) (numberFieldEncoding basis) target source
    (fun p=>prepare (p.1,p.2.value)) (ParameterizedMatrixEvaluation.answer MS US wS F) recover pre
    (Classical.choice hr) rawView (fun raw h=>(hs raw h).1)
  · intro raw h query hquery
    have hh:=hq ((rawView raw h).1,(rawView raw h).2.value) (hs raw h).2.1 (hs raw h).2.2 query hquery
    exact ⟨canonicalView query,canonicalView_encode ey query,hh.1,by simpa using hh.2⟩
  · intro query _
    exact value_encode basis ey MS US wS F allowedS query
  · intro raw h
    have hh:=correct ((rawView raw h).1,(rawView raw h).2.value) (hs raw h).2.1 (hs raw h).2.2
    change (numberFieldEncoding basis).encode (recover _)=target.value raw
    rw [hh]
    have hv:=ParameterizedMatrixEvaluation.value_raw_input basis ex MT UT wT B allowedT (rawView raw h)
    rw [(hs raw h).1] at hv
    exact hv.symm
  · exact simulation.output_length_bound

end PlanarHom.ParameterizedGraphReduction
