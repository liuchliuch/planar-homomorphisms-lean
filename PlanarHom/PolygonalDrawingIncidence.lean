import PlanarHom.PolygonalSegmentIncidence
import PlanarHom.PolygonalMidpointRefinement
import PlanarHom.PolygonalNormalAssignment

/-!
# Actual finite polygonal-drawing incidence

All straight pieces and host points are extracted from an existing ordinary
polygonal drawing. Non-host endpoints have the genuine unique incoming/outgoing
corner required by the numerical normal-selection theorem. No source incidence
certificate is assumed.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.MultiGraph.PolygonalDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- The actual set of directed straight pieces used by the finite edge chains. -/
def segmentSet (d : PolygonalDrawing G) : Set (Plane × Plane) :=
  {p | ∃ e, p ∈ (d.chain e).segments}

/-- Original graph vertices, which must remain pinched in any ribbon drawing. -/
def hostSet (d : PolygonalDrawing G) : Set Plane := Set.range d.drawing.point

/-- The ordinary drawing axioms give the full graph-arc equality classification. -/
theorem chain_graphArc (d : PolygonalDrawing G) (e : E) : Polygonal.GraphArc (d.chain e).strictPath := by
  intro s t heq
  have h : d.drawing.curve e s = d.drawing.curve e t := by
    simpa only [d.curve_eq] using heq
  by_cases hs0 : s = 0
  · subst s
    have ht := (d.drawing.curve_eq_point_iff e t (G.src e)).mp
      (h.symm.trans (d.drawing.curve_zero e))
    rcases ht with ⟨ht,_⟩ | ⟨ht,_⟩
    · exact Or.inl ht.symm
    · exact Or.inr (Or.inl ⟨rfl,ht⟩)
  · by_cases hs1 : s = 1
    · subst s
      have ht := (d.drawing.curve_eq_point_iff e t (G.dst e)).mp
        (h.symm.trans (d.drawing.curve_one e))
      rcases ht with ⟨ht,_⟩ | ⟨ht,_⟩
      · exact Or.inr (Or.inr ⟨rfl,ht⟩)
      · exact Or.inl ht.symm
    · have hsi := PlaneDrawing.inside_of_ne_endpoints hs0 hs1
      by_cases ht0 : t = 0
      · subst t
        exact (d.drawing.interior_avoids e s hsi (G.src e) (h.trans (d.drawing.curve_zero e))).elim
      · by_cases ht1 : t = 1
        · subst t
          exact (d.drawing.interior_avoids e s hsi (G.dst e) (h.trans (d.drawing.curve_one e))).elim
        · exact Or.inl (d.drawing.interior_injective e e s t hsi
            (PlaneDrawing.inside_of_ne_endpoints ht0 ht1) h).2

/-- A non-host point cannot belong to the drawn images of two different edges. -/
theorem edge_unique_at_nonhost (d : PolygonalDrawing G) {x : Plane} (hx : x ∉ d.hostSet)
    {e f : E} (he : x ∈ (d.chain e).support) (hf : x ∈ (d.chain f).support) : e = f := by
  rw [d.chain_support_eq_curve_range e] at he
  rw [d.chain_support_eq_curve_range f] at hf
  obtain ⟨s,hs⟩ := he
  obtain ⟨t,ht⟩ := hf
  have hinside (g : E) (u : I) (hu : d.drawing.curve g u = x) : Inside u := by
    apply PlaneDrawing.inside_of_ne_endpoints
    · intro h0
      subst u
      exact hx ⟨G.src g,(d.drawing.curve_zero g).symm.trans hu⟩
    · intro h1
      subst u
      exact hx ⟨G.dst g,(d.drawing.curve_one g).symm.trans hu⟩
  exact (d.drawing.interior_injective e f s t (hinside e s hs) (hinside f t ht)
    (hs.trans ht.symm)).1

/-- Every segment endpoint genuinely belongs to its edge's drawn support. -/
theorem endpoint_mem_chain_support (d : PolygonalDrawing G) {e : E} {a b x : Plane}
    (hab : (a,b) ∈ (d.chain e).segments) (hx : a = x ∨ b = x) : x ∈ (d.chain e).support := by
  apply (d.chain e).segment_subset_support hab
  rcases hx with rfl | rfl
  · exact left_mem_segment ℝ _ _
  · exact right_mem_segment ℝ _ _

/-- Directed valence two at every non-host endpoint is a theorem of the actual
finite drawing, including corners of closed-loop edge chains. -/
theorem twoValentCorners (d : PolygonalDrawing G) : Polygonal.TwoValentCorners d.segmentSet d.hostSet := by
  intro x hx htouch
  obtain ⟨a,b,⟨e,hab⟩,hax⟩ := htouch
  have hxe := d.endpoint_mem_chain_support hab hax
  have hxsrc : x ≠ d.drawing.point (G.src e) := fun h => hx ⟨G.src e,h.symm⟩
  have hxdst : x ≠ d.drawing.point (G.dst e) := fun h => hx ⟨G.dst e,h.symm⟩
  obtain ⟨P,Q,hPx,hxQ,hcorner,hout,hin⟩ := (d.chain e).graphArc_internal_incidence
    (d.chain_graphArc e) x hxsrc hxdst ⟨a,b,hab,hax⟩
  refine ⟨P,Q,hPx,hxQ,hcorner,?_,?_⟩
  · intro c d' ⟨f,hcd⟩ hc
    have hef := d.edge_unique_at_nonhost hx hxe (d.endpoint_mem_chain_support hcd (Or.inl hc))
    subst f
    exact hout c d' hcd hc
  · intro c d' ⟨f,hcd⟩ hd
    have hef := d.edge_unique_at_nonhost hx hxe (d.endpoint_mem_chain_support hcd (Or.inr hd))
    subst f
    exact hin c d' hcd hd

/-- All extracted segments are genuinely nondegenerate. -/
theorem segment_ne (d : PolygonalDrawing G) {a b : Plane} (hab : (a,b) ∈ d.segmentSet) : a ≠ b := by
  obtain ⟨e,he⟩ := hab
  exact (d.chain e).graphArc_segment_ne (d.chain_graphArc e) he

/-- A host vertex on a straight piece is one of its endpoints, never an interior point. -/
theorem host_segment_contact (d : PolygonalDrawing G) {a b x : Plane}
    (hab : (a,b) ∈ d.segmentSet) (hx : x ∈ d.hostSet) (hxs : x ∈ [a -[ℝ] b]) : a = x ∨ b = x := by
  obtain ⟨e,he⟩ := hab
  obtain ⟨v,rfl⟩ := hx
  rw [segment_eq_image_lineMap] at hxs
  obtain ⟨t,ht,hline⟩ := hxs
  by_cases ht0 : t = 0
  · exact Or.inl (by simpa [ht0] using hline)
  · by_cases ht1 : t = 1
    · exact Or.inr (by simpa [ht1] using hline)
    · obtain ⟨f,hf,hinside,hpath⟩ := (d.chain e).segment_subpath he
      let u : I := ⟨t,ht⟩
      have hu : Inside u := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),lt_of_le_of_ne ht.2 ht1⟩
      apply False.elim
      apply d.drawing.interior_avoids e (f u) (hinside u hu) v
      rw [d.curve_eq]
      exact (hpath u).trans hline

end PlanarHom.MultiGraph.PolygonalDrawing
