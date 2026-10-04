import PlanarHom.RootedOccurrenceTreeLookup
import PlanarHom.PlanarityLRChildInduction
import PlanarHom.PlanarityLRDrawnTree
import PlanarHom.PlanarityLRBackWords

/-! NEW actual finite DFS occurrence-tree builder. Children are the literal
finRange-filtered tree occurrences, and recursion consumes explicit Nat fuel. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints MultiGraph

abbrev DFSTree (g : MixedCode) := RootedOccurrenceTree (Fin g.vertices) (Fin g.edges.length)

def dfsSource (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (e : Fin g.edges.length) : Fin g.vertices :=
  ⟨source g e.val,(source_target_valid g hg e.isLt).1⟩
def dfsTarget (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (e : Fin g.edges.length) : Fin g.vertices :=
  ⟨target g e.val,(source_target_valid g hg e.isLt).2⟩

def dfsChildren (g : MixedCode) (v : Fin g.vertices) : List (Fin g.edges.length) :=
  (List.finRange g.edges.length).filter (fun e=>isTree g e.val && decide (source g e.val=v.val))

def dfsTreeAux (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) : ℕ→Fin g.vertices→DFSTree g
  | 0, v => .node v []
  | n+1, v => .node v ((dfsChildren g v).map (fun e=>(e,dfsTreeAux g hg n (dfsTarget g hg e))))

def dfsTree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) : DFSTree g :=
  dfsTreeAux g hg (g.vertices-height g v.val) v

@[simp] theorem dfsChildren_mem (g : MixedCode) (v : Fin g.vertices) (e : Fin g.edges.length) :
    e∈dfsChildren g v ↔ isTree g e.val=true ∧ source g e.val=v.val := by
  simp [dfsChildren]

theorem dfsChildren_nodup (g : MixedCode) (v : Fin g.vertices) : (dfsChildren g v).Nodup :=
  (List.nodup_finRange _).filter _

@[simp] theorem dfsTreeAux_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (n : ℕ) (v : Fin g.vertices) :
    (dfsTreeAux g hg n v).root=v := by cases n <;> simp [dfsTreeAux]
@[simp] theorem dfsTree_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) :
    (dfsTree g hg v).root=v := dfsTreeAux_root g hg _ v

 theorem dfs_child_fuel (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {n : ℕ} {v : Fin g.vertices} (hn : g.vertices-height g v.val≤n+1)
    {e : Fin g.edges.length} (he : e∈dfsChildren g v) :
    g.vertices-height g (dfsTarget g hg e).val≤n := by
  rcases (dfsChildren_mem g v e).mp he with ⟨ht,hs⟩
  have hh:=child_depth_remainder_lt g hg ht
  rw [hs] at hh
  change g.vertices-height g (target g e.val)≤n
  omega

 theorem desc_eq_or_child (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v w : Fin g.vertices) : Desc g v.val w.val ↔
    w=v ∨ ∃e∈dfsChildren g v,Desc g (dfsTarget g hg e).val w.val := by
  constructor
  · intro h
    rcases h with heq | hdesc
    · exact Or.inl (Fin.ext heq.symm)
    · obtain ⟨x,hx,hpar,hd,hheight⟩:=exists_child_toward g w.isLt hdesc
      have hpos:0<height g x:=by omega
      have hp:=parentEdge_tree g hg hx hpos
      let e:Fin g.edges.length:=⟨parentEdge g x,(of_decide_eq_true hp.1).1⟩
      refine Or.inr ⟨e,(dfsChildren_mem g v e).mpr ⟨hp.1,hp.2.2.trans hpar⟩,?_⟩
      simpa only [dfsTarget,e,hp.2.1] using hd
  · rintro (rfl | ⟨e,he,hd⟩)
    · exact Or.inl rfl
    · have hc:=(dfsChildren_mem g v e).mp he
      have hpar:=tree_source_ancestor g hg hc.1
      rw [hc.2] at hpar
      exact desc_trans g w.isLt (Or.inr hpar) hd

end PlanarHom.PlanarityLRDirect
