import PlanarHom.PlanarityFaceCache

namespace ReimplementedFaceTables
open PlanarHom.Complexity PlanarHom.PlanarityFaceCode PlanarHom.PlanarityRotationCode
open PlanarHom.PlanarityLRConstraints PlanarHom.ListPrefixMachines

def triangle : MixedCode := ⟨3,[(0,(1,0)),(0,(2,0)),(1,(2,0))],[]⟩
def k4 : MixedCode := ⟨4,[(0,(1,0)),(0,(2,0)),(0,(3,0)),(1,(2,0)),(1,(3,0)),(2,(3,0))],[]⟩
def loopParallel : MixedCode := ⟨2,[(0,(0,0)),(0,(1,0)),(0,(1,0))],[]⟩
def disconnected : MixedCode := ⟨5,[(0,(1,0)),(2,(3,0))],[]⟩
def isolated : MixedCode := ⟨4,[],[]⟩
def invalid : MixedCode := ⟨1,[(0,(1000000000000000000000000,0))],[]⟩

theorem prefix_zero (xs : List ℕ) : indexedTake xs 0=[] := by simp [indexedTake_eq]
theorem prefix_exact : indexedTake [5,4,3,2] 2=[5,4] := by decide
theorem empty_table : computedTable isolated=[] := by decide
example : FP MixedCode.encoding PlanarHom.MultiGraph.Kasteleyn.tableCode computedTable := fp_computedTable
example (g:MixedCode) (bits:List Bool) (a:Dart) : (boundary g bits a).length≤2*g.edges.length :=
  boundary_length g bits a

#eval indexedTake [5,4,3,2] 2
#eval indexedTake [5,4] 1000000000000000000000000
#eval ([1,2,5,3]:List ℕ).takeWhile (fun n=>decide (n<4))
#eval orbit triangle [false,false,false] (0,true)
#eval boundary triangle [false,false,false] (0,true)
#eval representatives triangle [false,false,false]
#eval cachedComputedTable triangle
#eval (cachedComputedTable k4).length
#eval cachedComputedTable loopParallel
#eval cachedComputedTable disconnected
#eval cachedComputedTable isolated
#eval orbit invalid [] (1000000000000000000000000000,false)
end ReimplementedFaceTables
