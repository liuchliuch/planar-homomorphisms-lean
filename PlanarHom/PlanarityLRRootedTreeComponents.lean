import PlanarHom.PlanarityLRRootedTreeValidity

/-! NEW exact recursive unfolding and computed-component specializations of the
literal finite DFS occurrence tree. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints MultiGraph RootedOccurrenceTree

 theorem dfsTree_eq_node (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) :
    dfsTree g hg v=.node v ((dfsChildren g v).map (fun e=>(e,dfsTree g hg (dfsTarget g hg e)))) := by
  have hv:=height_lt_vertices g v.isLt
  have hpos:0<g.vertices-height g v.val:=by omega
  obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  unfold dfsTree
  rw [hn,dfsTreeAux]
  congr 1
  apply List.map_congr_left
  intro e he
  have hc:=(dfsChildren_mem g v e).mp he
  have hh:=tree_height_succ g hg hc.1
  rw [hc.2] at hh
  have hnt:g.vertices-height g (dfsTarget g hg e).val=n := by
    change g.vertices-height g (target g e.val)=n
    omega
  rw [hnt]

 theorem dfsTree_childPairs (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) :
    (dfsTree g hg v).childPairs=(dfsChildren g v).map (fun e=>(e,dfsTree g hg (dfsTarget g hg e))) := by
  rw [dfsTree_eq_node]
  rfl

 theorem dfsTree_childLookup_of_mem (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v : Fin g.vertices) (e : Fin g.edges.length) (he : e∈dfsChildren g v) :
    (dfsTree g hg v).childLookup e=some (dfsTree g hg (dfsTarget g hg e)) := by
  apply (childLookup_eq_some_iff _ (dfsTree_valid g hg v) _ _).mpr
  rw [dfsTree_childPairs]
  exact List.mem_map.mpr ⟨e,he,rfl⟩

 theorem desc_root_iff_component (g : MixedCode) (r w : Fin g.vertices) (hr : height g r.val=0) :
    Desc g r.val w.val ↔ componentRoot g w.val=r.val := by
  constructor
  · intro hd
    have he:=componentRoot_eq_of_desc g w.isLt hd
    rw [componentRoot_eq_self g r.isLt hr] at he
    exact he.symm
  · intro he
    have hd:=(componentRoot_spec g w.isLt).2.1
    simpa only [he] using hd

 theorem dfsTree_root_vertices (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r w : Fin g.vertices) (hr : height g r.val=0) :
    w∈(dfsTree g hg r).vertices ↔ componentRoot g w.val=r.val := by
  rw [dfsTree_vertices,desc_root_iff_component g r w hr]

 theorem dfsTree_root_edges (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) (hr : height g r.val=0) (e : Fin g.edges.length) :
    e∈(dfsTree g hg r).edges ↔ isTree g e.val=true ∧ componentRoot g (source g e.val)=r.val := by
  rw [dfsTree_edges]
  exact and_congr_right (fun _=>desc_root_iff_component g r (dfsSource g hg e) hr)

 def dfsComponentTree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) : DFSTree g :=
   dfsTree g hg ⟨componentRoot g v.val,(componentRoot_spec g v.isLt).1⟩

 theorem dfsComponentTree_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) :
    (dfsComponentTree g hg v).Valid (dfsGraph g hg) := dfsTree_valid g hg _

 theorem dfsComponentTree_vertices (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v w : Fin g.vertices) : w∈(dfsComponentTree g hg v).vertices ↔ componentRoot g w.val=componentRoot g v.val :=
   dfsTree_root_vertices g hg _ w (componentRoot_spec g v.isLt).2.2

 theorem dfsComponentTree_edges (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v : Fin g.vertices) (e : Fin g.edges.length) :
    e∈(dfsComponentTree g hg v).edges ↔ isTree g e.val=true ∧ componentRoot g (source g e.val)=componentRoot g v.val :=
   dfsTree_root_edges g hg _ (componentRoot_spec g v.isLt).2.2 e

end PlanarHom.PlanarityLRDirect
