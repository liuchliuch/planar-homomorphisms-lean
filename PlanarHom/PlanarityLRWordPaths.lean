import PlanarHom.PlanarityLRComponents
import PlanarHom.PlanarityLRDirect

/-! NEW exact root-path and tree-word prefix structure, derived from literal DFS
ancestor snapshots. No tree representation or path oracle is assumed. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

 theorem rootPath_prefix_iff_desc (g : MixedCode) {u v : ℕ} (hv : v<g.vertices) :
    (rootPath g u).IsPrefix (rootPath g v) ↔ Desc g u v := by
  constructor
  · intro hp
    apply rootPath_mem_desc
    exact hp.subset (by simp [rootPath])
  · intro hd
    rcases hd with rfl | hd
    · exact ⟨[],by simp⟩
    · obtain ⟨pre,hpre⟩:=ancestors_suffix g hv hd
      refine ⟨pre.reverse++[v],?_⟩
      simp [rootPath,hpre,List.reverse_append,List.append_assoc]

 theorem rootPath_parent (g : MixedCode) {v : ℕ} (hv : v<g.vertices) (hh : 0<height g v) :
    rootPath g v=rootPath g (parentVertex g v)++[v] := by
  simp [rootPath,ancestors_parent g hv hh]

 theorem rootPath_eq_singleton (g : MixedCode) {v : ℕ} (hh : height g v=0) : rootPath g v=[v] := by
  have ha:ancestors g v=[] := List.length_eq_zero_iff.mp hh
  simp [rootPath,ha]

@[simp] theorem treeWord_length (g : MixedCode) (bits : List Bool) (v : ℕ) :
    (treeWord g bits v).length=height g v := by simp [treeWord]

 theorem treeWord_root (g : MixedCode) (bits : List Bool) {v : ℕ} (hh : height g v=0) :
    treeWord g bits v=[] := by simp [treeWord,rootPath_eq_singleton g hh]

 theorem treeWord_parent (g : MixedCode) (bits : List Bool) {v : ℕ}
    (hv : v<g.vertices) (hh : 0<height g v) :
    treeWord g bits v=treeWord g bits (parentVertex g v)++
      [(orderedOutgoing g bits (parentVertex g v)).idxOf (parentEdge g v)] := by
  have hl : 1≤(rootPath g (parentVertex g v)).length := by simp
  simp only [treeWord,rootPath_parent g hv hh,List.drop_append_of_le_length hl,List.map_append,List.map_singleton]

 theorem treeWord_prefix_of_desc (g : MixedCode) (bits : List Bool) {u v : ℕ}
    (hv : v<g.vertices) (hd : Desc g u v) : (treeWord g bits u).IsPrefix (treeWord g bits v) := by
  have hp:=(rootPath_prefix_iff_desc g hv).mpr hd
  exact (hp.drop 1).map _

 theorem parentEdge_mem_orderedOutgoing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) (hh : 0<height g v) :
    parentEdge g v∈orderedOutgoing g bits (parentVertex g v) := by
  rw [mem_orderedOutgoing]
  have ht:=parentEdge_tree g hg hv hh
  simp [outgoing,parentEdge_lt g hv hh,ht.1,ht.2.2]

end PlanarHom.PlanarityLRDirect
