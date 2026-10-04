import PlanarHom.PlanarityLRComponents
import PlanarHom.PlanarityRotationCode
import PlanarHom.PlanarRootedTreeExtraction
import PlanarHom.FisherTrianglePermutation

/-! NEW specialization of genuine drawing tree extraction to the exact raw DFS
forest, preserving all original edge occurrence indices. -/
noncomputable section
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints MultiGraph

def dfsGraph (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    MultiGraph (Fin g.vertices) (Fin g.edges.length) where
  src e := ⟨source g e.val,(source_target_valid g hg e.isLt).1⟩
  dst e := ⟨target g e.val,(source_target_valid g hg e.isLt).2⟩

def typedComponentTreeOrder (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : Fin g.vertices) :
    List (Fin g.edges.length) := (componentTreeOrder g r.val).attach.map
      (fun e => ⟨e.val,(of_decide_eq_true ((mem_componentTreeOrder g r.val e.val).mp e.property).1).1⟩)

theorem typedComponentTreeOrder_values (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) : (typedComponentTreeOrder g hg r).map Fin.val = componentTreeOrder g r.val := by
  simp [typedComponentTreeOrder,List.map_map,Function.comp_def,List.attach_map_subtype_val]

theorem typedComponentTreeOrder_rooted (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : Fin g.vertices) : (dfsGraph g hg).RootedInsertionOrder r (typedComponentTreeOrder g hg r) := by
  intro pre e post horder
  have hraw := congrArg (List.map Fin.val) horder
  rw [typedComponentTreeOrder_values,List.map_append,List.map_cons] at hraw
  have hs := componentTreeOrder_source_available g hg r.val hraw
  have ht := componentTreeOrder_target_fresh g hg r.val hraw
  refine ⟨?_,?_,?_⟩
  · rcases hs with hs | ⟨f,hf,hfs⟩
    · exact Or.inl (Fin.ext hs)
    · obtain ⟨f',hf',heq⟩ := List.mem_map.mp hf
      exact Or.inr ⟨f',hf',Fin.ext (by change target g f'.val = source g e.val; rw [heq]; exact hfs)⟩
  · intro h
    exact ht.1 (congrArg Fin.val h)
  · intro f hf
    have hh := ht.2 f.val (List.mem_map.mpr ⟨f,hf,rfl⟩)
    exact ⟨fun h => hh.1 (congrArg Fin.val h),fun h => hh.2 (congrArg Fin.val h)⟩

private theorem raw_src (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (e : Fin g.edges.length) :
    ((g.toMultiGraph hg).src e).val = (edge g e.val).1 := by
  simp [MixedCode.toMultiGraph,edge,List.getD_eq_getElem?_getD,e.isLt,List.get_eq_getElem]
private theorem raw_dst (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (e : Fin g.edges.length) :
    ((g.toMultiGraph hg).dst e).val = (edge g e.val).2.1 := by
  simp [MixedCode.toMultiGraph,edge,List.getD_eq_getElem?_getD,e.isLt,List.get_eq_getElem]

/-- Orient the same actual drawing along DFS; no planarity test or new drawing
certificate is called to decide the orientation. -/
def dfsDrawing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (D : PlaneDrawing (g.toMultiGraph hg)) : PlaneDrawing (dfsGraph g hg) :=
  D.reorient (fun e => decide (source g e.val ≠ (edge g e.val).1))
    (by
      intro e
      apply Fin.ext
      simp only [dfsGraph]
      split_ifs with h
      · simp only [decide_eq_true_eq] at h
        rw [raw_dst]
        rcases PlanarityRotationCode.source_target_endpoints g e.val with hh | hh
        · exact False.elim (h (congrArg Prod.fst hh))
        · exact congrArg Prod.fst hh
      · simp only [decide_eq_true_eq] at h
        rw [raw_src]
        exact Classical.not_not.mp h)
    (by
      intro e
      apply Fin.ext
      simp only [dfsGraph]
      split_ifs with h
      · simp only [decide_eq_true_eq] at h
        rw [raw_src]
        rcases PlanarityRotationCode.source_target_endpoints g e.val with hh | hh
        · exact False.elim (h (congrArg Prod.fst hh))
        · exact congrArg Prod.snd hh
      · simp only [decide_eq_true_eq] at h
        rw [raw_dst]
        rcases PlanarityRotationCode.source_target_endpoints g e.val with hh | hh
        · exact congrArg Prod.snd hh
        · have hs := congrArg Prod.fst hh
          have ht := congrArg Prod.snd hh
          have he := Classical.not_not.mp h
          simpa only [Prod.fst,Prod.snd] using ht.trans (he.symm.trans hs))

theorem dfsGraph_planar (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hp : (g.toMultiGraph hg).Planar) : (dfsGraph g hg).Planar := by
  obtain ⟨D⟩ := hp
  exact ⟨dfsDrawing g hg D⟩

/-- Ordinary planar validity yields a genuine chart of every computed DFS tree
component's actual polygonal support. The root and edge list are raw-computed. -/
theorem exists_computedTree_chart (g : MixedCode) {bt ut : ℕ} (hp : g.PlanarValid bt ut)
    (r : Fin g.vertices) :
    ∃ D : PolygonalDrawing (dfsGraph g hp.1),
      Nonempty ({x : Plane // x∉D.drawing.drawnTreeSupport r (typedComponentTreeOrder g hp.1 r)} ≃ₜ
        {y : Plane // y≠D.drawing.point r}) := by
  apply (dfsGraph_planar g hp.1 ((MixedCode.planarValid_iff g hp.1).mp hp)).exists_rootedTree_chart
  exact typedComponentTreeOrder_rooted g hp.1 r

end PlanarHom.PlanarityLRDirect
