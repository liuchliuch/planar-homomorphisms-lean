import PlanarHom.PlanarityDepthFirstSearch

namespace ReimplementedDFS
open PlanarHom.PlanarityDepthFirstSearch PlanarHom.Complexity

def triangle : MixedCode := ⟨3,[(0,(1,0)),(0,(2,0)),(1,(2,0))],[]⟩
def parallelLoop : MixedCode := ⟨3,[(0,(0,0)),(0,(1,0)),(0,(1,0))],[]⟩
def malformed : MixedCode := ⟨2,[(0,(987654321,0))],[]⟩
def empty : MixedCode := ⟨0,[],[]⟩

 theorem triangle_discovery : discoveryOrder triangle=[0,1,2] := by decide
 theorem triangle_finish : finishOrder triangle=[2,1,0] := by decide
 theorem triangle_depth_first_parent : parentEdge triangle 2=2 := by decide
 theorem triangle_ancestors : ancestors triangle 2=[1,0] := by decide
 theorem triangle_depth : height triangle 2=2 := by decide
 theorem loop_parallel_parent : parentEdge parallelLoop 1=1 := by decide
 theorem isolate_root : height parallelLoop 2=0 := by decide
 theorem empty_result : run empty=⟨[],[],[],[]⟩ := by decide

example (g:MixedCode) : (run g).work=[] := run_complete g
example (g:MixedCode) {u v:ℕ} (hu:u<g.vertices) (hv:v<g.vertices) (ha:Adjacent g u v) :
    u=v ∨ u∈ancestors g v ∨ v∈ancestors g u := adjacent_ancestor_comparable g hu hv ha

#eval discoveryOrder triangle
#eval finishOrder triangle
#eval ancestors triangle 2
#eval parentEdge triangle 2
#eval height triangle 2
#eval discoveryOrder parallelLoop
#eval finishOrder parallelLoop
#eval parentEdge parallelLoop 1
#eval ancestors parallelLoop 2
#eval discoveryOrder malformed
#eval finishOrder malformed
#eval (run empty).work

end ReimplementedDFS
