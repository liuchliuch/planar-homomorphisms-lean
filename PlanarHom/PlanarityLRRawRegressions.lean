import PlanarHom.PlanarityLRRawConstraints

/-! NEW raw-code executable LR-extraction tests. These check the concrete
algorithm; they do not replace the missing topological LR characterization. -/
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace PlanarHom.PlanarityLRRawConstraints.Regression
open Complexity PlanarityDepthFirstSearch

def completeGraph (n : ℕ) : MixedCode :=
  ⟨n,(List.range n).flatMap (fun u => ((List.range n).filter (fun v => decide (u<v))).map
    (fun v => (u,v,0))),[]⟩

def completeBipartite (n m : ℕ) : MixedCode :=
  ⟨n+m,(List.range n).flatMap (fun u => (List.range m).map (fun v => (u,v+n,0))),[]⟩

def parallelLoops : MixedCode := ⟨2,[(0,0,0),(0,1,0),(1,0,0),(1,1,0)],[]⟩

example : (solveLR (completeGraph 0)).1 = true := by decide
example : (solveLR (completeGraph 1)).1 = true := by decide
example : (solveLR (completeGraph 3)).1 = true := by decide
example : (solveLR parallelLoops).1 = true := by decide
example : (neighbours parallelLoops 0).length = 4 := by decide

/-- The kernel-checked successful raw execution satisfies every extracted fork. -/
theorem triangle_satisfies_extracted_forks :
    LRCondition (completeGraph 3) (PlanarityParitySolver.lookup (solveLR (completeGraph 3)).2) :=
  solveLR_sound _ (by decide)

#eval ((solveLR (completeGraph 3)).1,(solveLR (completeGraph 4)).1,
  (solveLR (completeGraph 5)).1,(solveLR (completeBipartite 3 3)).1)
#eval discoveryOrder parallelLoops
#eval (List.range 4).map (fun e => (isTree parallelLoops e,isBack parallelLoops e))

end PlanarHom.PlanarityLRRawConstraints.Regression
