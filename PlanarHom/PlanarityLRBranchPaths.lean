import PlanarHom.PlanarityLRNesting

/-! NEW exact child-branch lookup along actual saved DFS paths. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

private theorem chain_heights (g : MixedCode) {path : List ℕ} (h : Chain (run g).discovered path) :
    path.map (height g) = (List.range path.length).reverse := by
  induction h with
  | nil => rfl
  | cons r hr hc ih =>
    have he := discoveryAt_eq g hr
    have hh : height g r.vertex = r.ancestors.length := by simp [height,ancestors,he]
    simp only [List.map_cons,hh,ih,List.length_cons,List.range_succ,List.reverse_append,
      List.reverse_singleton,List.singleton_append]

/-- The root-to-vertex list has exactly depth 0,1,...,height(v). -/
def rootPath (g : MixedCode) (v : ℕ) : List ℕ := (v::ancestors g v).reverse

theorem rootPath_heights (g : MixedCode) {v : ℕ} (hv : v < g.vertices) :
    (rootPath g v).map (height g) = List.range (height g v+1) := by
  obtain ⟨hr,hrv⟩ := discoveryAt_mem g hv
  have hc := (stackInvariant_iterate g (fuel g)).record_chains _ hr
  have h := chain_heights g (Chain.cons (discoveryAt g v) hr hc)
  rw [hrv] at h
  have hh := congrArg List.reverse h
  simpa only [rootPath,List.map_reverse,List.reverse_reverse,List.length_cons,ancestors,height] using hh

@[simp] theorem rootPath_length (g : MixedCode) (v : ℕ) : (rootPath g v).length = height g v+1 := by
  simp [rootPath,height]

theorem rootPath_mem_desc (g : MixedCode) {u v : ℕ} (hu : u ∈ rootPath g v) : Desc g u v := by
  simpa only [rootPath,List.mem_reverse,List.mem_cons,Desc] using hu

theorem rootPath_getD_height (g : MixedCode) {v k : ℕ} (hv : v < g.vertices) (hk : k ≤ height g v) :
    height g ((rootPath g v).getD k v) = k := by
  have hl : k < (rootPath g v).length := by simp; omega
  have hmap := congrArg (fun xs : List ℕ => xs.getD k 0) (rootPath_heights g hv)
  have hget : (rootPath g v).getD k v = (rootPath g v)[k] := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,Option.getD_some]
  rw [hget]
  simpa [List.getD_eq_getElem?_getD,hl,show k < height g v+1 by omega] using hmap

theorem rootPath_getD_mem (g : MixedCode) (v k : ℕ) (hk : k ≤ height g v) :
    (rootPath g v).getD k v ∈ rootPath g v := by
  have hl : k < (rootPath g v).length := by simp; omega
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,Option.getD_some]
  exact List.getElem_mem hl

/-- Child immediately above the target of a back edge on its source path. -/
def branchChild (g : MixedCode) (b : ℕ) : ℕ :=
  (rootPath g (source g b)).getD (targetHeight g b+1) (source g b)

def branchEdge (g : MixedCode) (b : ℕ) : ℕ := parentEdge g (branchChild g b)

theorem branchChild_spec (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {b : ℕ} (hb : isBack g b = true) :
    branchChild g b < g.vertices ∧ Desc g (branchChild g b) (source g b) ∧
      height g (branchChild g b) = targetHeight g b+1 := by
  have hs := (source_target_valid g hg (of_decide_eq_true hb).1).1
  have hh := back_height_lt g hg hb
  have hm := rootPath_getD_mem g (source g b) (targetHeight g b+1) (by omega)
  have hd := rootPath_mem_desc g hm
  exact ⟨desc_valid g hs hd,hd,rootPath_getD_height g hs (by omega)⟩

/-- The branch child is literally parented at the back-edge target. -/
theorem branchChild_parent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {b : ℕ} (hb : isBack g b = true) : parentVertex g (branchChild g b) = target g b := by
  have hc := branchChild_spec g hg hb
  have hs := (source_target_valid g hg (of_decide_eq_true hb).1).1
  have ht := (source_target_valid g hg (of_decide_eq_true hb).1).2
  have hpos : 0 < height g (branchChild g b) := by omega
  have hp := parentVertex_ancestor g hc.1 hpos
  have hpd := desc_trans g hs (Or.inr hp) hc.2.1
  have htd : Desc g (target g b) (source g b) := Or.inr (back_target_ancestor g hg hb)
  have hph := parent_height g hc.1 hpos
  have heqh : height g (parentVertex g (branchChild g b)) = height g (target g b) := by
    change height g (branchChild g b) = height g (parentVertex g (branchChild g b))+1 at hph
    have hch := hc.2.2
    change height g (branchChild g b) = height g (target g b)+1 at hch
    omega
  rcases desc_comparable g hs hpd htd with h | h
  · rcases h with h | h
    · exact h
    · have hh := ancestors_height_lt g ht h
      omega
  · rcases h with h | h
    · exact h.symm
    · have hh := ancestors_height_lt g (desc_valid g hs hpd) h
      omega

/-- Reconstruct the actual directed tree occurrence from any nonroot vertex. -/
theorem parentEdge_tree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {v : ℕ} (hv : v < g.vertices) (hpos : 0 < height g v) :
    isTree g (parentEdge g v) = true ∧ target g (parentEdge g v) = v ∧
      source g (parentEdge g v) = parentVertex g v := by
  have hi := parentEdge_lt g hv hpos
  obtain ⟨e,he,hends⟩ := neighbours_occurrence g _ (parentEdge_incidence g hv hpos)
  have heq : edge g (parentEdge g v) = e := by
    simp only [edge,List.getD_eq_getElem?_getD,he,Option.getD_some]
  have hp := parentVertex_height_lt g hv hpos
  have hlu : lower g (parentEdge g v) = parentVertex g v ∧ upper g (parentEdge g v) = v := by
    rcases hends with ⟨hs,hd⟩ | ⟨hs,hd⟩
    · simp [lower,upper,heq,hs,hd,hp.le]
    · simp [lower,upper,heq,hs,hd,not_le_of_gt hp]
  have ht : isTree g (parentEdge g v) = true := by simp [isTree,hi,hlu.2,hpos]
  exact ⟨ht,by simpa [target,ht] using hlu.2,by simpa [source,ht] using hlu.1⟩

theorem branchEdge_spec (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {b : ℕ} (hb : isBack g b = true) :
    isTree g (branchEdge g b) = true ∧ source g (branchEdge g b) = target g b ∧
      target g (branchEdge g b) = branchChild g b := by
  have hc := branchChild_spec g hg hb
  have hh : 0 < height g (branchChild g b) := by omega
  have hp := parentEdge_tree g hg hc.1 hh
  exact ⟨hp.1,hp.2.2.trans (branchChild_parent g hg hb),hp.2.1⟩

end PlanarHom.PlanarityLRDirect
