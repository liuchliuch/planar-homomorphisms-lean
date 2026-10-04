import PlanarHom.PlanarityLRWordSubtrees

namespace ReimplementedLRWords
open PlanarHom.Complexity PlanarHom.PlanarityLRDirect PlanarHom.PlanarityLRRawConstraints
open PlanarHom.PlanarityDepthFirstSearch

def triangle : MixedCode := ⟨3,[(0,(1,0)),(0,(2,0)),(1,(2,0))],[]⟩
def k4 : MixedCode := ⟨4,[(0,(1,0)),(0,(2,0)),(0,(3,0)),(1,(2,0)),(1,(3,0)),(2,(3,0))],[]⟩
def twoTriangles : MixedCode := ⟨6,[(0,(1,0)),(0,(2,0)),(1,(2,0)),(3,(4,0)),(3,(5,0)),(4,(5,0))],[]⟩

theorem triangle_valid : triangle.Valid 1 1 := by simp [MixedCode.Valid,triangle]
example {b c : ℕ} (hb : isBack triangle b=true) (hc : isBack triangle c=true)
    (hr : componentRoot triangle (source triangle b)=componentRoot triangle (source triangle c))
    (hp : (backWord triangle [] b).IsPrefix (backWord triangle [] c)) : b=c :=
  backWord_prefix_free triangle triangle_valid [] hb hc hr hp
example {u v : ℕ} (hv : v<triangle.vertices) :
    (rootPath triangle u).IsPrefix (rootPath triangle v) ↔ Desc triangle u v := rootPath_prefix_iff_desc triangle hv

example {u b : ℕ} (hu : u<triangle.vertices) (hb : isBack triangle b=true)
    (hr : componentRoot triangle u=componentRoot triangle (source triangle b)) :
    (treeWord triangle [] u).IsPrefix (backWord triangle [] b) ↔ Desc triangle u (source triangle b) :=
  treeWord_prefix_backWord_iff_desc triangle triangle_valid [] hu hb hr

#eval (List.range 3).map (rootPath triangle)
#eval (List.range 3).map (treeWord triangle [])
#eval (List.range 6).filter (isBack k4)
#eval [1,2,4].map (backWord k4 [])
#eval let ws:=[1,2,4].map (backWord k4 []); ws.map (fun a=>ws.map (fun b=>a.isPrefixOf b))
#eval (rootPath triangle 1).isPrefixOf (rootPath triangle 2)
#eval (rootPath triangle 2).isPrefixOf (rootPath triangle 1)
#eval backWord twoTriangles [] 1 == backWord twoTriangles [] 4
#eval [componentRoot twoTriangles (source twoTriangles 1),componentRoot twoTriangles (source twoTriangles 4)]
end ReimplementedLRWords
