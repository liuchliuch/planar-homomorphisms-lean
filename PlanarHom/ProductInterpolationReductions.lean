import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.PreparedRecoveryCorrectness
import PlanarHom.PlanarRibbonExistence
import PlanarHom.OracleReductionComposition

/-! Actual raw-code polynomial-time product interpolation (Lemma3.1).
Every query, finite-word operation, field arithmetic step, coefficient update,
recovery operation and cumulative cost is compiled and proved. -/
namespace PlanarHom.Complexity.MixedCode
noncomputable section
open PlanarHom.ProductInterpolationPreparationMachines PlanarHom.ProductCompatibility
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {q dimension binaryTypes unaryTypes : ℕ}

/-- Binary interpolation on any exactly preserved graph promise. No algorithm
or bit-cost hypothesis occurs: the concrete preparation/recovery machines are
used, with source-zero and equal-product conditions matching Lemma3.1. -/
noncomputable def binaryProductReductionOn (basis : Module.Basis (Fin dimension) ℚ K)
    (M M' : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (selected : Fin binaryTypes) (H : MixedCode→Prop)
    (valid : ∀g,H g→g.Valid binaryTypes unaryTypes)
    (closed : ∀g,H g→∀n,H (g.parallelLabel selected.val n))
    (hunchanged : ∀l,l.val≠selected.val→M' l=M l)
    (hzero : ∀i j,M selected i j=0→M' selected i j=0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q=>M selected p.1 p.2)
      (fun p : Fin q × Fin q=>M' selected p.1 p.2)) :
    PromisePolyTimeTuringReduction (restrictedEvaluationProblem basis M' U w H)
      (restrictedEvaluationProblem basis M U w H):=by
  let A:=binaryAlphabet (M selected)
  let B:=binaryAlphabet (M' selected)
  apply reductionOfPipeline basis (metadataEncoding basis A) M' U w M U w H H valid valid
    (binaryPreparation A B selected.val) (recoverContext A)
    (fp_binaryPreparation basis A B selected.val) (fp_recover_context basis A)
  · intro g hg query hquery
    obtain ⟨n,_,_,rfl⟩:=PlanarHom.GraphInterpolationQueries.mem_queries hquery
    exact closed g hg n
  · intro g hg
    exact PlanarHom.PreparedRecoveryCorrectness.binary_preparation_recovery_correct g (valid g hg)
      selected M M' U w hunchanged hzero (compatible_of_hasProductMaps _ _ hproducts)

/-- Full ordinary-planar raw-code binary replacement. No ribbon drawing,
canonical input convention, arithmetic interface, or height premise is assumed. -/
noncomputable def binaryProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M M' : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (selected : Fin binaryTypes)
    (hunchanged : ∀l,l.val≠selected.val→M' l=M l)
    (hzero : ∀i j,M selected i j=0→M' selected i j=0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q=>M selected p.1 p.2)
      (fun p : Fin q × Fin q=>M' selected p.1 p.2)) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M' U w) (evaluationProblem basis M U w):=
  binaryProductReductionOn basis M M' U w selected (PlanarValid binaryTypes unaryTypes)
    (fun _ h=>h.1) (fun _ h n=>h.parallelLabel selected.val n) hunchanged hzero hproducts

/-- Unary counterpart on an exactly preserved promise; only the selected unary
occurrences change, and every binary label and background weight is unchanged. -/
noncomputable def unaryProductReductionOn (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U U' : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (selected : Fin unaryTypes) (H : MixedCode→Prop)
    (valid : ∀g,H g→g.Valid binaryTypes unaryTypes)
    (closed : ∀g,H g→∀n,H (g.parallelUnaryLabel selected.val n))
    (hunchanged : ∀l,l.val≠selected.val→U' l=U l)
    (hzero : ∀i,U selected i=0→U' selected i=0)
    (hproducts : HasProductMaps (U selected) (U' selected)) :
    PromisePolyTimeTuringReduction (restrictedEvaluationProblem basis M U' w H)
      (restrictedEvaluationProblem basis M U w H):=by
  apply reductionOfPipeline basis (metadataEncoding basis (U selected)) M U' w M U w H H valid valid
    (unaryPreparation (U selected) (U' selected) selected.val) (recoverContext (U selected))
    (fp_unaryPreparation basis (U selected) (U' selected) selected.val) (fp_recover_context basis (U selected))
  · intro g hg query hquery
    obtain ⟨n,_,_,rfl⟩:=PlanarHom.GraphInterpolationQueries.mem_queries hquery
    exact closed g hg n
  · intro g hg
    exact PlanarHom.PreparedRecoveryCorrectness.unary_preparation_recovery_correct g (valid g hg)
      selected M U U' w hunchanged hzero (compatible_of_hasProductMaps _ _ hproducts)

noncomputable def unaryProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U U' : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (selected : Fin unaryTypes)
    (hunchanged : ∀l,l.val≠selected.val→U' l=U l)
    (hzero : ∀i,U selected i=0→U' selected i=0)
    (hproducts : HasProductMaps (U selected) (U' selected)) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U' w) (evaluationProblem basis M U w):=
  unaryProductReductionOn basis M U U' w selected (PlanarValid binaryTypes unaryTypes)
    (fun _ h=>h.1) (fun _ h n=>h.parallelUnaryLabel selected.val n) hunchanged hzero hproducts

/-- Joint availability is inherited by genuine promise-reduction transitivity,
with all original companion binary/unary types still present in the instance. -/
noncomputable def binaryProduct_joint (basis : Module.Basis (Fin dimension) ℚ K)
    (M M' : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (selected : Fin binaryTypes)
    (hunchanged : ∀l,l.val≠selected.val→M' l=M l)
    (hzero : ∀i j,M selected i j=0→M' selected i j=0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q=>M selected p.1 p.2)
      (fun p : Fin q × Fin q=>M' selected p.1 p.2))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U w) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M' U w) base:=
  (binaryProductReduction basis M M' U w selected hunchanged hzero hproducts).trans available

noncomputable def unaryProduct_joint (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U U' : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (selected : Fin unaryTypes)
    (hunchanged : ∀l,l.val≠selected.val→U' l=U l)
    (hzero : ∀i,U selected i=0→U' selected i=0)
    (hproducts : HasProductMaps (U selected) (U' selected))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U w) base) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U' w) base:=
  (unaryProductReduction basis M U U' w selected hunchanged hzero hproducts).trans available

end
end PlanarHom.Complexity.MixedCode
