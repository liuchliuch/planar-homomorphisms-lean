import PlanarHom.EmbeddedSegmentTreeAttachment
import PlanarHom.PolygonalDrawingIncidence
import PlanarHom.PlanarEdgeOperations
import PlanarHom.PlanarPolygonalization

/-!
# NEW extraction of geometric trees from ordinary drawings and rooted edge lists

All segment contacts and chain simplicity are derived from the literal drawing.
The only combinatorial input is the actual parent-before-child/fresh-target
condition proved separately for raw DFS. No geometric tree/chart is an input.
-/
noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph
variable {X A : Type*} (G : MultiGraph X A)

/-- The combinatorial condition for inserting rooted tree edges one by one. -/
def RootedInsertionOrder (r : X) (es : List A) : Prop :=
  ∀ pre e post, es = pre ++ e::post →
    (G.src e=r ∨ ∃ f∈pre, G.dst f=G.src e) ∧
    G.dst e≠r ∧ ∀ f∈pre, G.dst e≠G.src f ∧ G.dst e≠G.dst f

namespace PlaneDrawing
variable {G}

def drawnTreeSupport (D : PlaneDrawing G) (r : X) (es : List A) : Set Plane :=
  {D.point r} ∪ ⋃ e∈es, Set.range (D.curve e)

/-- Fresh target labels and ordinary drawing disjointness force exact one-point
contact with the previous drawn tree. -/
theorem fresh_edge_contact (D : PlaneDrawing G) (r : X) (pre : List A) (e : A)
    (hr : G.dst e≠r)
    (hfresh : ∀ f∈pre, G.dst e≠G.src f ∧ G.dst e≠G.dst f) :
    ∀ x, x∈Set.range (D.curve e) → x∈D.drawnTreeSupport r pre → x=D.point (G.src e) := by
  intro x hx hS
  obtain ⟨s,hs⟩ := hx
  by_cases hs0 : s=0
  · exact hs.symm.trans (hs0 ▸ D.curve_zero e)
  have heold (f : A) (hf : f∈pre) : e≠f := by
    intro hh
    exact (hfresh f hf).2 (congrArg G.dst hh)
  by_cases hs1 : s=1
  · have hdst : D.point (G.dst e)=x := by simpa only [hs1,D.curve_one] using hs
    rcases hS with hroot | hold
    · exact False.elim (hr (D.point_injective (hdst.trans hroot)))
    · simp only [Set.mem_iUnion,Set.mem_range] at hold
      obtain ⟨f,hf,t,ht⟩ := hold
      rcases (D.curve_eq_point_iff f t (G.dst e)).mp (ht.trans hdst.symm) with ⟨_,hv⟩ | ⟨_,hv⟩
      · exact False.elim ((hfresh f hf).1 hv.symm)
      · exact False.elim ((hfresh f hf).2 hv.symm)
  · have hsi := inside_of_ne_endpoints hs0 hs1
    rcases hS with hroot | hold
    · exact False.elim (D.interior_avoids e s hsi r (hs.trans hroot))
    · simp only [Set.mem_iUnion,Set.mem_range] at hold
      obtain ⟨f,hf,t,ht⟩ := hold
      exact False.elim (D.interior_notMem_other_range (heold f hf) hsi ⟨t,ht.trans hs.symm⟩)

theorem drawnTreeSupport_nil (D : PlaneDrawing G) (r : X) :
    D.drawnTreeSupport r [] = {D.point r} := by simp [drawnTreeSupport]

theorem drawnTreeSupport_snoc (D : PlaneDrawing G) (r : X) (es : List A) (e : A) :
    D.drawnTreeSupport r (es++[e]) = D.drawnTreeSupport r es ∪ Set.range (D.curve e) := by
  ext x
  simp only [drawnTreeSupport,Set.mem_union,Set.mem_singleton_iff,Set.mem_iUnion,
    List.mem_append,List.mem_singleton]
  constructor
  · rintro (h | ⟨f,(hf | rfl),hx⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨f,hf,hx⟩)
    · exact Or.inr hx
  · rintro ((h | ⟨f,hf,hx⟩) | hx)
    · exact Or.inl h
    · exact Or.inr ⟨f,Or.inl hf,hx⟩
    · exact Or.inr ⟨e,Or.inr rfl,hx⟩

end PlaneDrawing

namespace PolygonalDrawing
variable {G}
local instance : DecidableEq Plane := Classical.decEq _

/-- Simplicity is a theorem of the literal nonloop drawing curve. -/
theorem nonloop_chain_simple (D : PolygonalDrawing G) (e : A) (hne : G.src e≠G.dst e) :
    (D.chain e).IsSimple := by
  apply (D.chain e).simple_of_strictPath_injective
  intro s t h
  rcases D.chain_graphArc e s t h with hh | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact hh
  · have hp : D.drawing.point (G.src e)=D.drawing.point (G.dst e) := by simpa [hs,ht] using h
    exact False.elim (hne (D.drawing.point_injective hp))
  · have hp : D.drawing.point (G.dst e)=D.drawing.point (G.src e) := by simpa [hs,ht] using h
    exact False.elim (hne (D.drawing.point_injective hp).symm)

/-- Extract a finite geometric tree directly from the ordinary polygonal drawing
and a combinatorial insertion order. The original curves are not replaced. -/
theorem exists_embeddedTree_of_rootedOrder (D : PolygonalDrawing G) (r : X) (es : List A)
    (horder : G.RootedInsertionOrder r es) :
    ∃ V E, EmbeddedSegmentTree (D.drawing.point r) V E ∧
      (∀ e∈es, D.drawing.point (G.dst e)∈V) ∧
      segmentTreeSupport V E = D.drawing.drawnTreeSupport r es := by
  induction es using List.reverseRecOn with
  | nil =>
      refine ⟨{D.drawing.point r},∅,EmbeddedSegmentTree.root,by simp,?_⟩
      simp [segmentTreeSupport,PlaneDrawing.drawnTreeSupport]
  | append_singleton es e ih =>
      have hpre : G.RootedInsertionOrder r es := by
        intro pre f post heq
        apply horder pre f (post++[e])
        simp only [heq,List.append_assoc,List.cons_append]
      obtain ⟨V,E,T,htargets,hS⟩ := ih hpre
      obtain ⟨hsource,hr,hfresh⟩ := horder es e [] (by simp)
      have ha : D.drawing.point (G.src e)∈V := by
        rcases hsource with hh | ⟨f,hf,hh⟩
        · rw [hh]; exact T.root_mem
        · rw [← hh]; exact htargets f hf
      have hne : G.src e≠G.dst e := by
        intro hh
        rcases hsource with hs | ⟨f,hf,hs⟩
        · exact hr (hh.symm.trans hs)
        · exact (hfresh f hf).2 (hh.symm.trans hs.symm)
      have hcontact : ∀ x, x∈(D.chain e).support → x∈segmentTreeSupport V E →
          x=D.drawing.point (G.src e) := by
        rw [D.chain_support_eq_curve_range,hS]
        exact D.drawing.fresh_edge_contact r es e hr hfresh
      obtain ⟨V',E',T',hV,hend,hunion⟩ := T.attach_simpleChain (D.chain e)
        (D.nonloop_chain_simple e hne) ha hcontact
      refine ⟨V',E',T',?_,?_⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hV (htargets f hf)
        · have hh : f=e := by simpa using hf
          simpa only [hh] using hend
      · rw [hunion,hS,D.chain_support_eq_curve_range,PlaneDrawing.drawnTreeSupport_snoc]

/-- The ambient collapse can additionally fix every selected compact set away
from the actual drawn tree, for example closed middles of non-tree edges. -/
theorem exists_rootedTree_properCollapse (D : PolygonalDrawing G) (r : X) (es : List A)
    (horder : G.RootedInsertionOrder r es) {K : Set Plane} (hK : IsCompact K)
    (hdis : Disjoint K (D.drawing.drawnTreeSupport r es)) :
    ∃ C : ProperPlaneCollapse (D.drawing.drawnTreeSupport r es) (D.drawing.point r),
      ∀ x∈K, C.map x=x := by
  obtain ⟨V,E,T,_,hS⟩ := D.exists_embeddedTree_of_rootedOrder r es horder
  have hd : Disjoint K (segmentTreeSupport V E) := by rw [hS]; exact hdis
  have hC := T.exists_properCollapse hK hd
  rw [hS] at hC
  exact hC

/-- Actual tree-complement chart, with no supplied geometric tree certificate. -/
theorem exists_rootedTree_complementHomeomorph (D : PolygonalDrawing G) (r : X) (es : List A)
    (horder : G.RootedInsertionOrder r es) :
    Nonempty ({x : Plane // x∉D.drawing.drawnTreeSupport r es} ≃ₜ
      {y : Plane // y≠D.drawing.point r}) := by
  obtain ⟨V,E,T,_,hS⟩ := D.exists_embeddedTree_of_rootedOrder r es horder
  obtain ⟨H⟩ := T.exists_complementHomeomorph
  have heq : (D.drawing.drawnTreeSupport r es)ᶜ = (segmentTreeSupport V E)ᶜ :=
    congrArg Set.compl hS.symm
  exact ⟨(Homeomorph.setCongr heq).trans H⟩

end PolygonalDrawing

/-- Finite ordinary planarity and a rooted combinatorial edge order suffice for
an actual tree-complement chart in a polygonal drawing. -/
theorem Planar.exists_rootedTree_chart {G : MultiGraph X A} [Finite X] [Finite A]
    (hG : G.Planar) (r : X) (es : List A) (horder : G.RootedInsertionOrder r es) :
    ∃ D : PolygonalDrawing G,
      Nonempty ({x : Plane // x∉D.drawing.drawnTreeSupport r es} ≃ₜ
        {y : Plane // y≠D.drawing.point r}) := by
  obtain ⟨D⟩ := hG.exists_polygonalDrawing
  exact ⟨D,D.exists_rootedTree_complementHomeomorph r es horder⟩

end PlanarHom.MultiGraph
