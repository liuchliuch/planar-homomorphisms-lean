import PlanarHom.ParameterizedGraphReduction
import PlanarHom.RestrictedMatrixFamilyReduction

/-! The genuine parameterized graph caller with exact semantic restrictions,
including intrinsic prescribed-domain records on every accepted raw input. -/
noncomputable section
namespace PlanarHom.RestrictedParameterizedGraphReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases MachineComposition ParameterizedGraphReduction
variable {X Y Meta K : Type} [Field K] [Algebra ℚ K]
variable {dimension q bt ut bs us : ℕ}

def reductionOfPipeline
    (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X) (ey : BitEncoding Y)
    (em : BitEncoding Meta)
    (MT : Fin bt→Matrix (Fin q) (Fin q) K) (UT : Fin ut→Fin q→K) (wT : Fin q→K)
    (MS : Fin bs→Matrix (Fin q) (Fin q) K) (US : Fin us→Fin q→K) (wS : Fin q→K)
    (B : X→Matrix (Fin q) (Fin q) K) (F : Y→Matrix (Fin q) (Fin q) K)
    (allowedT : X→Prop) (allowedS : Y→Prop) (HT HS : MixedCode→Prop)
    (prepare : X×MixedCode→Meta×List (Y×MixedCode)) (recover : Meta×List K→K)
    (hp : FP (ex.prod encoding) (em.prod (ey.prod encoding).list) prepare)
    (hr : FP (em.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover)
    (hq : ∀p,allowedT p.1→HT p.2→∀query∈(prepare p).2,
      allowedS query.1 ∧ HS query.2)
    (correct : ∀p,allowedT p.1→HT p.2→
      recover ((prepare p).1,(prepare p).2.map (ParameterizedMatrixEvaluation.answer MS US wS F))=
        ParameterizedMatrixEvaluation.answer MT UT wT B p)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.targetProblem basis ey MS US wS F allowedS HS) base) :
    PromisePolyTimeTuringReduction (RestrictedMatrixFamilyReduction.targetProblem basis ex MT UT wT B allowedT HT)
      (RestrictedMatrixFamilyReduction.targetProblem basis ey MS US wS F allowedS HS) := by
  let target := RestrictedMatrixFamilyReduction.targetProblem basis ex MT UT wT B allowedT HT
  let source := RestrictedMatrixFamilyReduction.targetProblem basis ey MS US wS F allowedS HS
  let rawView : (raw : Bits)→target.valid raw→X×BitEncoding.ValidWord encoding := fun raw h=>Classical.choose h
  have hs : ∀raw (h : target.valid raw),
      (ParameterizedMatrixEvaluation.inputEncoding ex).encode (rawView raw h)=raw ∧
        allowedT (rawView raw h).1 ∧ HT (rawView raw h).2.value :=
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

end PlanarHom.RestrictedParameterizedGraphReduction
