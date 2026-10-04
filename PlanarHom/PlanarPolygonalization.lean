import PlanarHom.PlanarCorridors
import PlanarHom.PolygonalAttachments
import PlanarHom.PlanarPolygonalDrawing

/-!
# Every finite ordinary plane drawing has a finite polygonal redrawing

This constructs the redrawing through compactly separated vertex neighborhoods,
straight radial half-edge tails, disjoint connected open middle corridors,
actual finite polygonal loop erasure and first-contact tail attachment. Loops and
parallel occurrences retain the ordinary drawing conditions. Vertex positions
are unchanged. No polygonal approximation or plane-tameness theorem is assumed.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom
namespace Polygonal.GraphArc
variable {X : Type*} [NormedAddCommGroup X] {x y : X} {p : Path x y}

theorem interior_injective (h : GraphArc p) {s t : I}
    (hs : MultiGraph.Inside s) (_ht : MultiGraph.Inside t) (heq : p s = p t) : s = t := by
  rcases h s t heq with hst | ⟨hs0,_⟩ | ⟨hs1,_⟩
  · exact hst
  · simp [MultiGraph.Inside,hs0] at hs
  · simp [MultiGraph.Inside,hs1] at hs

theorem interior_ne_source (h : GraphArc p) {s : I} (hs : MultiGraph.Inside s) : p s ≠ x := by
  intro heq
  rcases h s 0 (heq.trans p.source.symm) with hs0 | ⟨hs0,_⟩ | ⟨hs1,_⟩
  · simp [MultiGraph.Inside,hs0] at hs
  · simp [MultiGraph.Inside,hs0] at hs
  · simp [MultiGraph.Inside,hs1] at hs

theorem interior_ne_target (h : GraphArc p) {s : I} (hs : MultiGraph.Inside s) : p s ≠ y := by
  intro heq
  rcases h s 1 (heq.trans p.target.symm) with hs1 | ⟨hs0,_⟩ | ⟨hs1,_⟩
  · simp [MultiGraph.Inside,hs1] at hs
  · simp [MultiGraph.Inside,hs0] at hs
  · simp [MultiGraph.Inside,hs1] at hs
end Polygonal.GraphArc

namespace MultiGraph.PlaneDrawing.Trimming.Corridors
variable {V E : Type*} {G : MultiGraph V E} {d : PlaneDrawing G} {r : ℝ}
variable {T : d.Trimming r} (C : T.Corridors)

/-- The region assigned to one redrawn edge, including its two straight tails. -/
def edgeEnvelope (e : E) : Set Plane :=
  T.radial (e,false) ∪ C.region e ∪ T.radial (e,true)

/-- A radial segment contains just its own original vertex. -/
theorem radial_vertex_identification (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {p : E × Bool} {v : V} (h : d.point v ∈ T.radial p) : v = T.portVertex p := by
  by_contra hv
  have hsep := d.radius_vertex_separation hr hv
  have hball : dist (d.point v) (d.point (T.portVertex p)) ≤ r :=
    T.radial_subset_closedBall hr0 p h
  linarith

/-- Only the prescribed endpoints are original vertices in an edge's envelope. -/
theorem envelope_vertex_identification (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {e : E} {v : V} (h : d.point v ∈ C.edgeEnvelope e) : v = G.src e ∨ v = G.dst e := by
  rcases h with (h | h) | h
  · exact Or.inl (radial_vertex_identification hr0 hr h)
  · exact (C.vertex_notMem e v h).elim
  · exact Or.inr (radial_vertex_identification hr0 hr h)

private theorem radial_envelope_intersection (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {p : E × Bool} {f : E} (hpf : p.1 ≠ f) {x : Plane}
    (hp : x ∈ T.radial p) (hf : x ∈ C.edgeEnvelope f) : ∃ v, x = d.point v := by
  rcases hf with (hf | hf) | hf
  · have hne : p ≠ (f,false) := fun h => hpf (congrArg Prod.fst h)
    exact ⟨T.portVertex p,(T.radial_intersection_vertex hr0 hr hne hp hf).2⟩
  · exact (Set.disjoint_left.mp (C.disjoint_other_radial hpf) hf hp).elim
  · have hne : p ≠ (f,true) := fun h => hpf (congrArg Prod.fst h)
    exact ⟨T.portVertex p,(T.radial_intersection_vertex hr0 hr hne hp hf).2⟩

/-- Different redrawn edges can meet only at original vertices. -/
theorem envelope_intersection (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {e f : E} (hef : e ≠ f) {x : Plane}
    (he : x ∈ C.edgeEnvelope e) (hf : x ∈ C.edgeEnvelope f) : ∃ v, x = d.point v := by
  rcases he with (he | he) | he
  · exact C.radial_envelope_intersection hr0 hr hef he hf
  · rcases hf with (hf | hf) | hf
    · exact (Set.disjoint_left.mp (C.disjoint_other_radial (p := (f,false)) hef.symm) he hf).elim
    · exact (Set.disjoint_left.mp (C.pairwise_disjoint e f hef) he hf).elim
    · exact (Set.disjoint_left.mp (C.disjoint_other_radial (p := (f,true)) hef.symm) he hf).elim
  · exact C.radial_envelope_intersection hr0 hr hef he hf

/-- A genuine finite polygonal edge inside its assigned geometric envelope.
The proof handles coincident endpoints by retaining only the endpoint repeat. -/
theorem exists_polygonal_edge (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v)) (e : E) :
    ∃ q : Polygonal.Chain Set.univ (d.point (G.src e)) (d.point (G.dst e)),
      Polygonal.GraphArc q.strictPath ∧ q.support ⊆ C.edgeEnvelope e := by
  obtain ⟨p,hp,_,_⟩ := C.exists_simple_middle e
  obtain ⟨q,hq,hsub⟩ := Polygonal.exists_attached_graphArc p hp
    (C.vertex_notMem e (G.src e)) (C.vertex_notMem e (G.dst e)) (by
      intro x hS hD
      have hne : (e,false) ≠ (e,true) := by simp
      have h := T.radial_intersection_vertex hr0 hr hne hS hD
      exact ⟨h.2,congrArg d.point h.1⟩)
  exact ⟨q,hq,hsub⟩

/-- Assemble all polygonal edges into an ordinary plane drawing. -/
def polygonalDrawing (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v)) : PolygonalDrawing G := by
  choose q hq hsub using C.exists_polygonal_edge hr0 hr
  have hsupp (e : E) (t : I) : (q e).strictPath t ∈ C.edgeEnvelope e := by
    apply hsub e
    rw [← Polygonal.Chain.range_strictPath]
    exact ⟨t,rfl⟩
  have havoid (e : E) (t : I) (ht : Inside t) (v : V) : (q e).strictPath t ≠ d.point v := by
    intro h
    have hv := C.envelope_vertex_identification hr0 hr (h ▸ hsupp e t)
    rcases hv with hv | hv
    · subst v
      exact (hq e).interior_ne_source ht h
    · subst v
      exact (hq e).interior_ne_target ht h
  let newDrawing : PlaneDrawing G := {
    point := d.point
    point_injective := d.point_injective
    curve := fun e => (q e).strictPath.toContinuousMap
    curve_zero := fun e => (q e).strictPath.source
    curve_one := fun e => (q e).strictPath.target
    interior_injective := by
      intro e f s t hs ht h
      by_cases hef : e = f
      · subst f
        exact ⟨rfl,(hq e).interior_injective hs ht h⟩
      · obtain ⟨v,hv⟩ := C.envelope_intersection hr0 hr hef (hsupp e s)
          (show (q e).strictPath s ∈ C.edgeEnvelope f by change (q e).strictPath s = (q f).strictPath t at h; rw [h]; exact hsupp f t)
        exact (havoid e s hs v hv).elim
    interior_avoids := havoid }
  exact ⟨newDrawing,q,fun _ => rfl⟩

end MultiGraph.PlaneDrawing.Trimming.Corridors

namespace MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Unconditional polygonal redrawing of an arbitrary finite ordinary drawing. -/
theorem exists_polygonalDrawing [Finite V] [Finite E] (d : PlaneDrawing G) :
    Nonempty (PolygonalDrawing G) := by
  obtain ⟨r,hr0,hr⟩ := d.exists_vertex_radius
  let T := d.trimming hr0 hr
  obtain ⟨C⟩ := T.exists_corridors hr0 hr
  exact ⟨C.polygonalDrawing hr0 hr⟩

end MultiGraph.PlaneDrawing
namespace MultiGraph

/-- Ordinary abstract finite planarity implies an explicit polygonal drawing. -/
theorem Planar.exists_polygonalDrawing {V E : Type*} [Finite V] [Finite E]
    {G : MultiGraph V E} (h : G.Planar) : Nonempty (PolygonalDrawing G) := by
  obtain ⟨d⟩ := h
  exact d.exists_polygonalDrawing

/-- Polygonal witnesses and ordinary topological drawings define the same finite
multigraph planarity predicate. No certificate is added to graph-code inputs. -/
theorem planar_iff_polygonalDrawing {V E : Type*} [Finite V] [Finite E] (G : MultiGraph V E) :
    G.Planar ↔ Nonempty (PolygonalDrawing G) :=
  ⟨Planar.exists_polygonalDrawing,fun ⟨p⟩ => p.planar⟩

end MultiGraph
end PlanarHom
