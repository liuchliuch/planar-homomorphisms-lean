import PlanarHom.PlanarityDepthFirstSearchMachines

/-! NEW reconstructed ordinary-input DFS package: the actual executable forest,
its exact encoded polynomial runtime, and the genuine no-cross-edge property. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity

 theorem certifiedDFS : FP MixedCode.encoding stateCode run ∧
    ∀g:MixedCode, (run g).work=[] ∧
      (∀v, v<g.vertices → (discoveryAt g v).vertex=v ∧ (ancestors g v).Nodup ∧
        ∀u∈ancestors g v,u<g.vertices ∧ height g u<height g v) ∧
      (∀u v, u<g.vertices → v<g.vertices → Adjacent g u v →
        u=v ∨ u∈ancestors g v ∨ v∈ancestors g u) := by
  refine ⟨fp_run,fun g=>⟨run_complete g,?_,?_⟩⟩
  · intro v hv
    exact ⟨(discoveryAt_mem g hv).2,ancestors_nodup g hv,
      fun u hu=>⟨ancestors_valid g hv hu,ancestors_height_lt g hv hu⟩⟩
  · exact fun u v hu hv ha=>adjacent_ancestor_comparable g hu hv ha

end PlanarHom.PlanarityDepthFirstSearch
