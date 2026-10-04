import PlanarHom.GraphComponentSemantics
import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.MaterializedFieldListMachines

/-! The actual component-query reduction, including raw input normalization,
charged oracle batching, and exact field multiplication of the answers. -/
noncomputable section
namespace PlanarHom.GraphComponentCode
open Complexity Complexity.MixedCode ArithmeticCircuitPrimitives PairProjectionMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension b u : ℕ}

/-- The oracle promise consists of nonempty connected ordinary planar codes. -/
def connectedEvaluationProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K) : PromiseProblem :=
  restrictedEvaluationProblem basis M U w
    (fun g => g.PlanarValid b u ∧ (support g).Connected ∧ 0<g.vertices)

/-- Query the genuinely computed connected components, then multiply their
answers. Empty graphs make no oracle calls and return the empty product `1`.
All successful alternate raw encodings are covered by the source promise. -/
def componentReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U w)
      (connectedEvaluationProblem basis M U w) := by
  apply reductionOfPipeline basis BitEncoding.bits M U w M U w
    (MixedCode.PlanarValid b u)
    (fun g => g.PlanarValid b u ∧ (support g).Connected ∧ 0<g.vertices)
    (fun _ hg => hg.1) (fun _ hg => hg.1.1)
    (fun g => ([],components g)) (fun p : Bits × List K => p.2.prod)
  · exact (fp_const MixedCode.encoding BitEncoding.bits []).pair GraphComponentMachines.fp_components
  · exact (fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
      (MaterializedFieldListMachines.fp_product basis)
  · exact components_promises
  · intro g hg
    exact (evaluate_components g hg.1 M U w).symm

end PlanarHom.GraphComponentCode
