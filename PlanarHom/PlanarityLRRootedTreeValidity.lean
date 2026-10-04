import PlanarHom.PlanarityLRRootedTreeMembership

/-! NEW compatibility and true vertex nodup for the actual recursive DFS tree. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints MultiGraph RootedOccurrenceTree

 theorem dfsTreeAux_compatible (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (n : ℕ) (v : Fin g.vertices) : (dfsTreeAux g hg n v).Compatible (dfsGraph g hg) := by
  induction n generalizing v with
  | zero => simp [dfsTreeAux]
  | succ n ih =>
    rw [dfsTreeAux,compatible_node]
    intro c hc
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hc
    refine ⟨Fin.ext ((dfsChildren_mem g v e).mp he).2,?_,ih (dfsTarget g hg e)⟩
    simp only [dfsTreeAux_root]
    rfl

 theorem dfs_children_common_descendant (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {v w : Fin g.vertices} {e f : Fin g.edges.length}
    (he : e∈dfsChildren g v) (hf : f∈dfsChildren g v)
    (hew : Desc g (dfsTarget g hg e).val w.val) (hfw : Desc g (dfsTarget g hg f).val w.val) : e=f := by
  have hes:=(dfsChildren_mem g v e).mp he
  have hfs:=(dfsChildren_mem g v f).mp hf
  have heh:=tree_height_succ g hg hes.1
  have hfh:=tree_height_succ g hg hfs.1
  rw [hes.2] at heh
  rw [hfs.2] at hfh
  have hheight:height g (target g e.val)=height g (target g f.val):=heh.trans hfh.symm
  have htarget:target g e.val=target g f.val := by
    rcases desc_comparable g w.isLt hew hfw with h | h
    · exact desc_eq_of_height_eq g (dfsTarget g hg f).isLt h hheight
    · exact (desc_eq_of_height_eq g (dfsTarget g hg e).isLt h hheight.symm).symm
  exact Fin.ext (tree_target_injective g hg hes.1 hfs.1 htarget)

 theorem dfsTreeAux_vertices_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (n : ℕ) (v : Fin g.vertices) (hn : g.vertices-height g v.val≤n) :
    (dfsTreeAux g hg n v).vertices.Nodup := by
  induction n generalizing v with
  | zero => have hh:=height_lt_vertices g v.isLt; omega
  | succ n ih =>
    rw [dfsTreeAux,vertices_node,List.nodup_cons]
    constructor
    · intro hv
      obtain ⟨c,hc,hv⟩:=List.mem_flatMap.mp hv
      obtain ⟨e,he,rfl⟩:=List.mem_map.mp hc
      have hd:=(dfsTreeAux_vertices g hg n (dfsTarget g hg e) (dfs_child_fuel g hg hn he) v).mp hv
      have hs:=(dfsChildren_mem g v e).mp he
      have hheight:=tree_height_succ g hg hs.1
      rw [hs.2] at hheight
      rcases hd with hd | hd
      · change target g e.val=v.val at hd
        rw [hd] at hheight
        omega
      · have hh:=ancestors_height_lt g v.isLt hd
        change height g (target g e.val)<height g v.val at hh
        omega
    · rw [List.nodup_flatMap]
      constructor
      · intro c hc
        obtain ⟨e,he,rfl⟩:=List.mem_map.mp hc
        exact ih (dfsTarget g hg e) (dfs_child_fuel g hg hn he)
      · apply List.pairwise_map.mpr
        apply (dfsChildren_nodup g v).imp_of_mem
        intro e f he hf hef w hwe hwf
        apply hef
        exact dfs_children_common_descendant g hg he hf
          ((dfsTreeAux_vertices g hg n (dfsTarget g hg e) (dfs_child_fuel g hg hn he) w).mp hwe)
          ((dfsTreeAux_vertices g hg n (dfsTarget g hg f) (dfs_child_fuel g hg hn hf) w).mp hwf)

 theorem dfsTree_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) :
    (dfsTree g hg v).Valid (dfsGraph g hg) :=
   ⟨dfsTreeAux_compatible g hg _ v,dfsTreeAux_vertices_nodup g hg _ v le_rfl⟩

end PlanarHom.PlanarityLRDirect
