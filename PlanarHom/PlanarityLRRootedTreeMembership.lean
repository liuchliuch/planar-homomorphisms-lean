import PlanarHom.PlanarityLRRootedTreeProgram

/-! NEW exact vertex and occurrence-edge membership of the actual fuelled DFS
tree builder, with the sufficient fuel proved from computed heights. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints MultiGraph RootedOccurrenceTree

 theorem dfsTreeAux_vertices (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (n : ℕ) (v : Fin g.vertices) (hn : g.vertices-height g v.val≤n) (w : Fin g.vertices) :
    w∈(dfsTreeAux g hg n v).vertices ↔ Desc g v.val w.val := by
  induction n generalizing v with
  | zero => have hh:=height_lt_vertices g v.isLt; omega
  | succ n ih =>
    rw [dfsTreeAux,vertices_node,desc_eq_or_child g hg v w]
    constructor
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · obtain ⟨c,hc,hw⟩:=List.mem_flatMap.mp h
        obtain ⟨e,he,rfl⟩:=List.mem_map.mp hc
        exact Or.inr ⟨e,he,(ih (dfsTarget g hg e) (dfs_child_fuel g hg hn he)).mp hw⟩
    · rintro (h | ⟨e,he,hw⟩)
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨(e,dfsTreeAux g hg n (dfsTarget g hg e)),List.mem_map.mpr ⟨e,he,rfl⟩,
            (ih (dfsTarget g hg e) (dfs_child_fuel g hg hn he)).mpr hw⟩)

 theorem dfsTreeAux_edges (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (n : ℕ) (v : Fin g.vertices) (hn : g.vertices-height g v.val≤n) (e : Fin g.edges.length) :
    e∈(dfsTreeAux g hg n v).edges ↔ isTree g e.val=true ∧ Desc g v.val (source g e.val) := by
  induction n generalizing v with
  | zero => have hh:=height_lt_vertices g v.isLt; omega
  | succ n ih =>
    rw [dfsTreeAux,edges_node]
    constructor
    · intro h
      obtain ⟨c,hc,he⟩:=List.mem_flatMap.mp h
      obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hc
      rcases List.mem_cons.mp he with rfl | he
      · have hs:=(dfsChildren_mem g v e).mp hf
        exact ⟨hs.1,Or.inl hs.2.symm⟩
      · have hs:=(dfsChildren_mem g v f).mp hf
        have hh:=(ih (dfsTarget g hg f) (dfs_child_fuel g hg hn hf)).mp he
        have hp:=tree_source_ancestor g hg hs.1
        rw [hs.2] at hp
        exact ⟨hh.1,desc_trans g (source_target_valid g hg e.isLt).1 (Or.inr hp) hh.2⟩
    · rintro ⟨ht,hd⟩
      rcases (desc_eq_or_child g hg v (dfsSource g hg e)).mp hd with heq | ⟨f,hf,hd⟩
      · have he:e∈dfsChildren g v:=(dfsChildren_mem g v e).mpr ⟨ht,congrArg Fin.val heq⟩
        exact List.mem_flatMap.mpr ⟨(e,dfsTreeAux g hg n (dfsTarget g hg e)),
          List.mem_map.mpr ⟨e,he,rfl⟩,List.mem_cons_self ..⟩
      · exact List.mem_flatMap.mpr ⟨(f,dfsTreeAux g hg n (dfsTarget g hg f)),
          List.mem_map.mpr ⟨f,hf,rfl⟩,List.mem_cons_of_mem _
            ((ih (dfsTarget g hg f) (dfs_child_fuel g hg hn hf)).mpr ⟨ht,hd⟩)⟩

 theorem dfsTree_vertices (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v w : Fin g.vertices) : w∈(dfsTree g hg v).vertices ↔ Desc g v.val w.val :=
   dfsTreeAux_vertices g hg _ v le_rfl w

 theorem dfsTree_edges (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v : Fin g.vertices) (e : Fin g.edges.length) :
    e∈(dfsTree g hg v).edges ↔ isTree g e.val=true ∧ Desc g v.val (source g e.val) :=
   dfsTreeAux_edges g hg _ v le_rfl e

end PlanarHom.PlanarityLRDirect
