import PlanarHom.PlanarityFaceRootCache

namespace ReimplementedFaceRoots
open PlanarHom.Complexity PlanarHom.PlanarityFaceCode PlanarHom.PlanarityRotationCode
open PlanarHom.PlanarityLRDirect

def triangle : MixedCode := ⟨3,[(0,(1,0)),(0,(2,0)),(1,(2,0))],[]⟩
def loopParallel : MixedCode := ⟨2,[(0,(0,0)),(0,(1,0)),(0,(1,0))],[]⟩
def disconnected : MixedCode := ⟨5,[(0,(1,0)),(2,(3,0))],[]⟩
def twoLoops : MixedCode := ⟨3,[(0,(0,0)),(1,(1,0))],[]⟩
def isolated : MixedCode := ⟨4,[],[]⟩

example : FP MixedCode.encoding PlanarHom.MultiGraph.Kasteleyn.logCode orientationLog := fp_orientationLog
example (g:MixedCode) : (orientationLog g).length≤2*g.edges.length := orientationLog_length g
example (g:MixedCode) (bits:List Bool) : (boundedTable g bits).Sublist (fullTable g bits) := boundedTable_sublist g bits

theorem zero_edges_log : orientationLog isolated=[] := by decide
#eval (List.range 5).map (componentRoot disconnected)
#eval cachedComputedBoundedTable triangle
#eval cachedOrientationLog triangle
#eval cachedComputedBoundedTable loopParallel
#eval cachedOrientationLog loopParallel
#eval cachedComputedBoundedTable disconnected
#eval cachedOrientationLog disconnected
#eval cachedComputedBoundedTable twoLoops
#eval cachedOrientationLog twoLoops
#eval cachedComputedBoundedTable isolated
#eval cachedOrientationLog isolated
end ReimplementedFaceRoots
