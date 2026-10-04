import PlanarHom.PlanarityLRConstraintMachines

namespace ReimplementedRawLR
open PlanarHom.Complexity PlanarHom.PlanarityLRConstraints

def completeGraph (n:ℕ) : MixedCode :=
  ⟨n,(List.range n).flatMap (fun u=>((List.range n).filter (fun v=>decide (u<v))).map (fun v=>(u,v,0))),[]⟩
def bipartite33 : MixedCode :=
  ⟨6,(List.range 3).flatMap (fun u=>(List.range 3).map (fun v=>(u,v+3,0))),[]⟩
def loopParallel : MixedCode := ⟨2,[(0,(0,0)),(0,(1,0)),(0,(1,0))],[]⟩
def empty : MixedCode := ⟨0,[],[]⟩
def isolated : MixedCode := ⟨3,[],[]⟩

 theorem empty_accepts : decideAligned empty=(true,[]) := by decide
 theorem isolated_accepts : decideAligned isolated=(true,[]) := by decide
 theorem loop_parallel_output_length : (decideAligned loopParallel).2.length=3 := by
  exact decideAligned_length loopParallel

example : FP MixedCode.encoding (BitEncoding.bool.prod BitEncoding.bool.list) decideAligned := fp_decideAligned

#eval (decideAligned (completeGraph 3)).1
#eval (decideAligned (completeGraph 4)).1
#eval (decideAligned (completeGraph 5)).1
#eval (decideAligned bipartite33).1
#eval (decideAligned loopParallel).1
#eval (decideAligned empty).1
#eval (decideAligned isolated).1
#eval (decideAligned (completeGraph 4)).2.length
#eval (decideAligned bipartite33).2.length
#eval (decideAligned loopParallel).2.length

end ReimplementedRawLR
