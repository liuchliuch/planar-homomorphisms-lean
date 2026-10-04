import PlanarHom.EndpointLoopSemantics
import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.MaterializedFieldListMachines

/-! Actual joint availability of D^k A D^k from k source loops at each
endpoint, including marked input loops and arbitrary retained companions. -/
noncomputable section
namespace PlanarHom.EndpointLoopMachines
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {b u dimension : ℕ}

def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) (old : Fin b) (k : ℕ) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M (decorated (M old) k)) U w)
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits (appendOne M (decorated (M old) k)) U w M U w
    (fun g=>([],[transform old k g])) (fun p : Bits×List K=>p.2.sum)
  · have hl := ((fp_transform old k).pair (fp_const encoding encoding.list [])).comp
      (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query=transform old k g := List.mem_singleton.mp hq
    subst query
    exact transform_planar old k g hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (transform_planar old k g hg).1]
    exact evaluate_transform old k g hg.1 M U w (transform_planar old k g hg).1

end PlanarHom.EndpointLoopMachines
