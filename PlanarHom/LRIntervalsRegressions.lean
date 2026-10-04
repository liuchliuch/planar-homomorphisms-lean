import PlanarHom.PlanarityLRBranchEventOrder

namespace ReimplementedLRIntervals
open PlanarHom.Complexity PlanarHom.PlanarityLRDirect PlanarHom.PlanarityLRRawConstraints
open PlanarHom.PlanarityDepthFirstSearch

def branchGraph : MixedCode := ⟨6,
  [(0,(1,0)),(0,(2,0)),(0,(3,0)),(1,(2,0)),(1,(3,0)),(2,(3,0)),
   (0,(4,0)),(0,(5,0)),(4,(5,0))],[]⟩

theorem branchGraph_valid : branchGraph.Valid 1 1 := by simp [MixedCode.Valid,branchGraph]
example {v a b c : ℕ} (hv : v<branchGraph.vertices)
    (ha : isBack branchGraph a=true) (hb : isBack branchGraph b=true) (hc : isBack branchGraph c=true)
    (hr : componentRoot branchGraph v=componentRoot branchGraph (source branchGraph b))
    (hva : Desc branchGraph v (source branchGraph a)) (hvc : Desc branchGraph v (source branchGraph c))
    (hab : (backEvents branchGraph []).idxOf a≤(backEvents branchGraph []).idxOf b)
    (hbc : (backEvents branchGraph []).idxOf b≤(backEvents branchGraph []).idxOf c) :
    Desc branchGraph v (source branchGraph b) :=
  subtree_event_interval branchGraph branchGraph_valid [] hv ha hb hc hr hva hvc hab hbc

#eval backEvents branchGraph []
#eval (backEvents branchGraph []).map (backWord branchGraph [])
#eval (backEvents branchGraph []).map (fun b=>(b,ancestor branchGraph 1 (source branchGraph b)))
#eval (backEvents branchGraph []).map (fun b=>(b,ancestor branchGraph 3 (source branchGraph b)))
#eval orderedOutgoing branchGraph [] 0
#eval [(orderedOutgoing branchGraph [] 0).idxOf 0,(orderedOutgoing branchGraph [] 0).idxOf 6]
#eval (backEvents branchGraph []).map (fun b=>(b,(backEvents branchGraph []).idxOf b))
#eval ([0,0]:List ℕ).isPrefixOf (backWord branchGraph [] 4)
#eval ([0,0]:List ℕ).isPrefixOf (backWord branchGraph [] 7)
end ReimplementedLRIntervals
