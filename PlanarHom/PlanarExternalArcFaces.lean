import PlanarHom.PlanarEdgeOperations
import PlanarHom.PlanarPolygonalDrawing
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Complementary arcs witness actual cofaciality

Deleting an added edge leaves its open curve inside a single actual
complementary component; continuity puts both endpoints in that component's
closure. This transfers cofaciality through an augmented polygonal redrawing.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- An actual complementary curve witnesses the closure-based face condition. -/
theorem cofacial_of_external_curve (d : PlaneDrawing G) {u v : V}
    (p : C(I,Plane)) (hzero : p 0 = d.point u) (hone : p 1 = d.point v)
    (havoid : ∀ t, Inside t → p t ∉ d.support) : d.Cofacial u v := by
  let S : Set Plane := p '' Set.Ioo (0 : I) 1
  have hmem : p firstThird ∈ S := ⟨firstThird,firstThird_inside,rfl⟩
  have hsub : S ⊆ d.supportᶜ := by
    rintro x ⟨t,ht,rfl⟩
    exact havoid t ht
  have hconnected : IsPreconnected S :=
    isPreconnected_Ioo.image p p.continuous.continuousOn
  have hface : S ⊆ connectedComponentIn d.supportᶜ (p firstThird) :=
    hconnected.subset_connectedComponentIn hmem hsub
  refine ⟨p firstThird,havoid _ firstThird_inside,?_,?_⟩
  · rw [← hzero]
    apply closure_mono hface
    apply mem_closure_image p.continuous.continuousAt
    rw [closure_Ioo (show (0 : I) ≠ 1 by norm_num)]
    exact ⟨le_rfl,bot_le⟩
  · rw [← hone]
    apply closure_mono hface
    apply mem_closure_image p.continuous.continuousAt
    rw [closure_Ioo (show (0 : I) ≠ 1 by norm_num)]
    exact ⟨bot_le,le_rfl⟩

/-- Forget exactly the newly added edge occurrence. -/
def withoutAddedEdge {u v : V} (d : PlaneDrawing (G.withEdge u v)) : PlaneDrawing G where
  point := d.point
  point_injective := d.point_injective
  curve e := d.curve (Sum.inl e)
  curve_zero e := d.curve_zero (Sum.inl e)
  curve_one e := d.curve_one (Sum.inl e)
  interior_injective := by
    intro e f s t hs ht heq
    obtain ⟨hef,hst⟩ := d.interior_injective (Sum.inl e) (Sum.inl f) s t hs ht heq
    exact ⟨Sum.inl.inj hef,hst⟩
  interior_avoids e t ht w := d.interior_avoids (Sum.inl e) t ht w

/-- The added edge's open curve misses the complete retained drawing. -/
theorem addedEdge_avoids {u v : V} (d : PlaneDrawing (G.withEdge u v))
    (t : I) (ht : Inside t) : d.curve (Sum.inr ()) t ∉ d.withoutAddedEdge.support := by
  rintro (⟨w,hw⟩ | hx)
  · exact d.interior_avoids _ t ht w hw.symm
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp hx
    exact d.interior_notMem_other_range (by simp) ht he

/-- Deleting an occurrence certifies actual cofaciality of its two ends. -/
theorem withoutAddedEdge_cofacial {u v : V} (d : PlaneDrawing (G.withEdge u v)) :
    d.withoutAddedEdge.Cofacial u v :=
  d.withoutAddedEdge.cofacial_of_external_curve (d.curve (Sum.inr ()))
    (d.curve_zero (Sum.inr ())) (d.curve_one (Sum.inr ())) d.addedEdge_avoids

end PlanarHom.MultiGraph.PlaneDrawing

namespace PlanarHom.MultiGraph.PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Forgetting the additional occurrence keeps the actual polygonal chains. -/
def withoutAddedEdge {u v : V} (d : PolygonalDrawing (G.withEdge u v)) : PolygonalDrawing G where
  drawing := d.drawing.withoutAddedEdge
  chain e := d.chain (Sum.inl e)
  curve_eq e := d.curve_eq (Sum.inl e)

theorem withoutAddedEdge_cofacial {u v : V} (d : PolygonalDrawing (G.withEdge u v)) :
    d.withoutAddedEdge.drawing.Cofacial u v := d.drawing.withoutAddedEdge_cofacial

end PlanarHom.MultiGraph.PolygonalDrawing
