import PlanarHom.PlanarPolygonalization

/-!
# Polygonal assembly from separated radial cores

A reusable geometric assembly lemma. Every input records actual compact core
sets, endpoint positions and proved intersections. The augmentation construction
instantiates these data from the original ordinary drawing.
-/

noncomputable section
open Set unitInterval Metric
open Classical
open scoped Convex
namespace PlanarHom.MultiGraph
variable {V E : Type*} (G : MultiGraph V E)

/-- The vertex associated with a directed half-edge. -/
def halfVertex (p : E × Bool) : V := if p.2 then G.dst p.1 else G.src p.1

/-- Actual compact cores with straight tails, before choosing their open corridors. -/
structure RadialCoreGeometry where
  point : V → Plane
  point_injective : Function.Injective point
  port : E × Bool → Plane
  port_injective : Function.Injective port
  middle : E → Set Plane
  isCompact_middle : ∀ e, IsCompact (middle e)
  isConnected_middle : ∀ e, IsConnected (middle e)
  port_mem_middle : ∀ p, port p ∈ middle p.1
  middle_disjoint : ∀ {e f}, e ≠ f → Disjoint (middle e) (middle f)
  point_notMem_middle : ∀ e v, point v ∉ middle e
  radial_vertex : ∀ {p v}, point v ∈ [point (G.halfVertex p) -[ℝ] port p] → v = G.halfVertex p
  radial_intersection : ∀ {p q x}, p ≠ q →
    x ∈ [point (G.halfVertex p) -[ℝ] port p] →
    x ∈ [point (G.halfVertex q) -[ℝ] port q] →
    G.halfVertex p = G.halfVertex q ∧ x = point (G.halfVertex p)
  middle_radial_intersection : ∀ {e p x}, x ∈ middle e →
    x ∈ [point (G.halfVertex p) -[ℝ] port p] → e = p.1 ∧ x = port p

/-- Metric separation conditions suffice for the exact radial intersection data. -/
def RadialCoreGeometry.ofMetric
    (point : V → Plane) (point_injective : Function.Injective point)
    (rho : V → ℝ) (hpos : ∀ v, 0 < rho v)
    (hballs : ∀ {v w}, v ≠ w →
      Disjoint (Metric.closedBall (point v) (rho v)) (Metric.closedBall (point w) (rho w)))
    (port : E × Bool → Plane) (port_injective : Function.Injective port)
    (hsphere : ∀ p, dist (port p) (point (G.halfVertex p)) = rho (G.halfVertex p))
    (middle : E → Set Plane)
    (hcompact : ∀ e, IsCompact (middle e)) (hconnected : ∀ e, IsConnected (middle e))
    (hport : ∀ p, port p ∈ middle p.1)
    (hdisjoint : ∀ {e f}, e ≠ f → Disjoint (middle e) (middle f))
    (houtside : ∀ e x, x ∈ middle e → ∀ v, rho v ≤ dist x (point v)) :
    RadialCoreGeometry G where
  point := point
  point_injective := point_injective
  port := port
  port_injective := port_injective
  middle := middle
  isCompact_middle := hcompact
  isConnected_middle := hconnected
  port_mem_middle := hport
  middle_disjoint := hdisjoint
  point_notMem_middle := by
    intro e v hv
    have := houtside e (point v) hv v
    exact (not_lt_of_ge (by simpa only [dist_self] using this) (hpos v))
  radial_vertex := by
    intro p v hv
    by_contra hne
    have hball : point v ∈ Metric.closedBall (point (G.halfVertex p)) (rho (G.halfVertex p)) :=
      (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self (hpos _).le)
        (hsphere p).le hv
    exact Set.disjoint_left.mp (hballs hne)
      (Metric.mem_closedBall_self (hpos v).le) hball
  radial_intersection := by
    intro p q x hpq hxp hxq
    by_cases hv : G.halfVertex p = G.halfVertex q
    · refine ⟨hv,?_⟩
      exact MultiGraph.radial_intersection (hpos _) (hsphere p)
        (by rw [hv,hsphere]) (port_injective.ne hpq) hxp (by simpa only [hv] using hxq)
    · have hpball : x ∈ Metric.closedBall (point (G.halfVertex p)) (rho (G.halfVertex p)) :=
        (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self (hpos _).le)
          (hsphere p).le hxp
      have hqball : x ∈ Metric.closedBall (point (G.halfVertex q)) (rho (G.halfVertex q)) :=
        (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self (hpos _).le)
          (hsphere q).le hxq
      exact (Set.disjoint_left.mp (hballs hv) hpball hqball).elim
  middle_radial_intersection := by
    intro e p x hx hp
    have heq : x = port p := radial_boundary_unique (hpos _) (hsphere p) hp
      (houtside e x hx _)
    refine ⟨?_,heq⟩
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint hne) hx (heq.symm ▸ hport p)

namespace RadialCoreGeometry
variable {G} (T : RadialCoreGeometry G)

def radial (p : E × Bool) : Set Plane := [T.point (G.halfVertex p) -[ℝ] T.port p]

theorem isCompact_radial (p : E × Bool) : IsCompact (T.radial p) := by
  rw [radial,segment_eq_image_lineMap]
  exact isCompact_Icc.image (by fun_prop)

theorem middle_disjoint_other_radial {e : E} {p : E × Bool} (he : e ≠ p.1) :
    Disjoint (T.middle e) (T.radial p) := by
  apply Set.disjoint_left.mpr
  intro x hx hp
  exact he (T.middle_radial_intersection hx hp).1

/-- Closed sets a middle-arc perturbation must avoid. -/
def corridorForbidden (e : E) : Set Plane :=
  Set.range T.point ∪ ⋃ p : {p : E × Bool // p.1 ≠ e}, T.radial p.1

theorem isCompact_corridorForbidden [Finite V] [Finite E] (e : E) :
    IsCompact (T.corridorForbidden e) :=
  (Set.finite_range T.point).isCompact.union
    (isCompact_iUnion (fun p => T.isCompact_radial p.1))

theorem middle_disjoint_corridorForbidden (e : E) :
    Disjoint (T.middle e) (T.corridorForbidden e) := by
  apply Set.disjoint_left.mpr
  rintro x hx (⟨v,rfl⟩ | hrad)
  · exact T.point_notMem_middle e v hx
  · obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hrad
    exact Set.disjoint_left.mp (T.middle_disjoint_other_radial (Ne.symm p.2)) hx hp

/-- Geometric neighborhoods, with every separation conclusion proved below. -/
structure Corridors where
  region : E → Set Plane
  isOpen : ∀ e, IsOpen (region e)
  isConnected : ∀ e, IsConnected (region e)
  contains_middle : ∀ e, T.middle e ⊆ region e
  pairwise_disjoint : ∀ e f, e ≠ f → Disjoint (region e) (region f)
  avoids_forbidden : ∀ e, region e ⊆ (T.corridorForbidden e)ᶜ

/-- Actual existence of connected open corridors from finite ordinary drawing
data. No planar-neighborhood theorem is assumed. -/
theorem exists_corridors [Finite V] [Finite E] :
    Nonempty T.Corridors := by
  letI : LocallyConnectedSpace Plane :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr (by
      intro x U hU
      obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hU
      exact ⟨Metric.ball x ε,hsub,isOpen_ball,Metric.mem_ball_self hε,
        (convex_ball x ε).isConnected ⟨x,Metric.mem_ball_self hε⟩⟩)
  have hforbid : ∀ e, ∃ ε : ℝ, 0 < ε ∧
      thickening ε (T.middle e) ⊆ (T.corridorForbidden e)ᶜ := by
    intro e
    apply (T.isCompact_middle e).exists_thickening_subset_open
      (T.isCompact_corridorForbidden e).isClosed.isOpen_compl
    exact disjoint_left.mp (T.middle_disjoint_corridorForbidden e)
  have hpair : ∀ p : E × E, ∃ ε : ℝ, 0 < ε ∧
      (p.1 ≠ p.2 → Disjoint (thickening ε (T.middle p.1)) (thickening ε (T.middle p.2))) := by
    rintro ⟨e,f⟩
    by_cases h : e = f
    · exact ⟨1,zero_lt_one,fun he => (he h).elim⟩
    · obtain ⟨ε,hε,hdis⟩ := (T.middle_disjoint h).exists_thickenings
        (T.isCompact_middle e) (T.isCompact_middle f).isClosed
      exact ⟨ε,hε,fun _ => hdis⟩
  choose a ha havoid using hforbid
  choose b hb hdis using hpair
  obtain ⟨α,hα,hαa⟩ := PlaneDrawing.finite_positive_lower_bound a ha
  obtain ⟨β,hβ,hβb⟩ := PlaneDrawing.finite_positive_lower_bound b hb
  let δ := min α β
  have hδ : 0 < δ := lt_min hα hβ
  let B : E → Set Plane := fun e => thickening δ (T.middle e)
  let U : E → Set Plane := fun e => connectedComponentIn (B e) (T.port (e,false))
  have hKB : ∀ e, T.middle e ⊆ B e := fun e => self_subset_thickening hδ _
  have hKU : ∀ e, T.middle e ⊆ U e := fun e =>
    (T.isConnected_middle e).isPreconnected.subset_connectedComponentIn (T.port_mem_middle (e,false)) (hKB e)
  have hBU : ∀ e, U e ⊆ B e := fun e => connectedComponentIn_subset _ _
  refine ⟨⟨U,?_,?_,hKU,?_,?_⟩⟩
  · intro e
    exact (isOpen_thickening : IsOpen (B e)).connectedComponentIn
  · intro e
    exact isConnected_connectedComponentIn_iff.mpr (hKB e (T.port_mem_middle (e,false)))
  · intro e f hef
    have hδb : δ ≤ b (e,f) := (min_le_right _ _).trans (hβb (e,f))
    exact (hdis (e,f) hef).mono
      ((hBU e).trans (thickening_mono hδb _))
      ((hBU f).trans (thickening_mono hδb _))
  · intro e
    exact (hBU e).trans ((thickening_mono ((min_le_left _ _).trans (hαa e)) _).trans (havoid e))

namespace Corridors
variable {T : RadialCoreGeometry G} (C : T.Corridors)

theorem vertex_notMem (e : E) (v : V) : T.point v ∉ C.region e := by
  intro h
  exact C.avoids_forbidden e h (Or.inl ⟨v,rfl⟩)

theorem disjoint_other_radial {e : E} {p : E × Bool} (he : p.1 ≠ e) :
    Disjoint (C.region e) (T.radial p) := by
  apply Set.disjoint_left.mpr
  intro x hx hp
  exact C.avoids_forbidden e hx (Or.inr (Set.mem_iUnion.mpr ⟨⟨p,he⟩,hp⟩))

theorem left_mem (e : E) : T.port (e,false) ∈ C.region e :=
  C.contains_middle e (T.port_mem_middle (e,false))

theorem right_mem (e : E) : T.port (e,true) ∈ C.region e :=
  C.contains_middle e (T.port_mem_middle (e,true))

/-- Genuine simple finite polygonal middle paths in the disjoint corridors. -/
theorem exists_simple_middle (e : E) :
    ∃ p : Polygonal.Chain (C.region e) (T.port (e,false)) (T.port (e,true)),
      p.IsSimple ∧ Function.Injective p.strictPath ∧ Set.range p.strictPath ⊆ C.region e := by
  apply Polygonal.exists_injective_polygonal_arc (C.isOpen e) (C.isConnected e).isPreconnected
    (C.left_mem e) (C.right_mem e)
  exact T.port_injective.ne (by simp)

end Corridors

namespace Corridors
variable {T : RadialCoreGeometry G} (C : T.Corridors)

/-- The region assigned to one redrawn edge, including its two straight tails. -/
def edgeEnvelope (e : E) : Set Plane :=
  T.radial (e,false) ∪ C.region e ∪ T.radial (e,true)

/-- Only the prescribed endpoints are original vertices in an edge's envelope. -/
theorem envelope_vertex_identification
    {e : E} {v : V} (h : T.point v ∈ C.edgeEnvelope e) : v = G.src e ∨ v = G.dst e := by
  rcases h with (h | h) | h
  · exact Or.inl (T.radial_vertex h)
  · exact (C.vertex_notMem e v h).elim
  · exact Or.inr (T.radial_vertex h)

private theorem radial_envelope_intersection
    {p : E × Bool} {f : E} (hpf : p.1 ≠ f) {x : Plane}
    (hp : x ∈ T.radial p) (hf : x ∈ C.edgeEnvelope f) : ∃ v, x = T.point v := by
  rcases hf with (hf | hf) | hf
  · have hne : p ≠ (f,false) := fun h => hpf (congrArg Prod.fst h)
    exact ⟨G.halfVertex p,(T.radial_intersection hne hp hf).2⟩
  · exact (Set.disjoint_left.mp (C.disjoint_other_radial hpf) hf hp).elim
  · have hne : p ≠ (f,true) := fun h => hpf (congrArg Prod.fst h)
    exact ⟨G.halfVertex p,(T.radial_intersection hne hp hf).2⟩

/-- Different redrawn edges can meet only at original vertices. -/
theorem envelope_intersection
    {e f : E} (hef : e ≠ f) {x : Plane}
    (he : x ∈ C.edgeEnvelope e) (hf : x ∈ C.edgeEnvelope f) : ∃ v, x = T.point v := by
  rcases he with (he | he) | he
  · exact C.radial_envelope_intersection hef he hf
  · rcases hf with (hf | hf) | hf
    · exact (Set.disjoint_left.mp (C.disjoint_other_radial (p := (f,false)) hef.symm) he hf).elim
    · exact (Set.disjoint_left.mp (C.pairwise_disjoint e f hef) he hf).elim
    · exact (Set.disjoint_left.mp (C.disjoint_other_radial (p := (f,true)) hef.symm) he hf).elim
  · exact C.radial_envelope_intersection hef he hf

/-- A genuine finite polygonal edge inside its assigned geometric envelope.
The proof handles coincident endpoints by retaining only the endpoint repeat. -/
theorem exists_polygonal_edge (e : E) :
    ∃ q : Polygonal.Chain Set.univ (T.point (G.src e)) (T.point (G.dst e)),
      Polygonal.GraphArc q.strictPath ∧ q.support ⊆ C.edgeEnvelope e := by
  obtain ⟨p,hp,_,_⟩ := C.exists_simple_middle e
  obtain ⟨q,hq,hsub⟩ := Polygonal.exists_attached_graphArc p hp
    (C.vertex_notMem e (G.src e)) (C.vertex_notMem e (G.dst e)) (by
      intro x hS hD
      have hne : (e,false) ≠ (e,true) := by simp
      have h := T.radial_intersection hne hS hD
      exact ⟨h.2,congrArg T.point h.1⟩)
  exact ⟨q,hq,hsub⟩

/-- Assemble all polygonal edges into an ordinary plane drawing. -/
def polygonalDrawing : PolygonalDrawing G := by
  choose q hq hsub using C.exists_polygonal_edge
  have hsupp (e : E) (t : I) : (q e).strictPath t ∈ C.edgeEnvelope e := by
    apply hsub e
    rw [← Polygonal.Chain.range_strictPath]
    exact ⟨t,rfl⟩
  have havoid (e : E) (t : I) (ht : Inside t) (v : V) : (q e).strictPath t ≠ T.point v := by
    intro h
    have hv := C.envelope_vertex_identification (h ▸ hsupp e t)
    rcases hv with hv | hv
    · subst v
      exact (hq e).interior_ne_source ht h
    · subst v
      exact (hq e).interior_ne_target ht h
  let newDrawing : PlaneDrawing G := {
    point := T.point
    point_injective := T.point_injective
    curve := fun e => (q e).strictPath.toContinuousMap
    curve_zero := fun e => (q e).strictPath.source
    curve_one := fun e => (q e).strictPath.target
    interior_injective := by
      intro e f s t hs ht h
      by_cases hef : e = f
      · subst f
        exact ⟨rfl,(hq e).interior_injective hs ht h⟩
      · obtain ⟨v,hv⟩ := C.envelope_intersection hef (hsupp e s)
          (show (q e).strictPath s ∈ C.edgeEnvelope f by change (q e).strictPath s = (q f).strictPath t at h; rw [h]; exact hsupp f t)
        exact (havoid e s hs v hv).elim
    interior_avoids := havoid }
  exact ⟨newDrawing,q,fun _ => rfl⟩


end Corridors

/-- Polygonal drawing assembled from the verified finite radial geometry. -/
theorem exists_polygonalDrawing [Finite V] [Finite E] (T : RadialCoreGeometry G) : Nonempty (PolygonalDrawing G) := by
  obtain ⟨C⟩ := T.exists_corridors
  exact ⟨C.polygonalDrawing⟩

end RadialCoreGeometry
end PlanarHom.MultiGraph
