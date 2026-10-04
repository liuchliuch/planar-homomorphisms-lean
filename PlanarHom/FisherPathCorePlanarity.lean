import PlanarHom.FisherMonotonePath
import PlanarHom.FisherTrimmedCurves

/-! A drawing-derived noncrossing vertex-path expansion before the two
pendant loop gadgets are attached. Original isolates are retained separately. -/
noncomputable section
open Classical Set unitInterval
open scoped Convex

namespace PlanarHom.Fisher
open MultiGraph
variable {V E : Type*} {G : MultiGraph V E}

abbrev PathCoreVertex (o : G.IncidenceOrdering) :=
  (Σ v, Fin (o.degree v)) ⊕ {v : V // o.degree v = 0}
abbrev PathCoreEdge (o : G.IncidenceOrdering) := E ⊕ (Σ v, Fin (o.degree v - 1))

def pathCoreGraph (o : G.IncidenceOrdering) :
    MultiGraph (PathCoreVertex o) (PathCoreEdge o) where
  src := Sum.elim (fun e => Sum.inl (o.darts.symm (e, false)))
    (fun q => Sum.inl ⟨q.1, pathSource q.2⟩)
  dst := Sum.elim (fun e => Sum.inl (o.darts.symm (e, true)))
    (fun q => Sum.inl ⟨q.1, pathTarget q.2⟩)

namespace PathCoreGeometry
variable {d : PlaneDrawing G} {r : ℝ} (T : d.Trimming r) (o : G.IncidenceOrdering)

def portPoint (v : V) (i : Fin (o.degree v)) : Plane := T.port (o.darts ⟨v,i⟩)

theorem portPoint_distance (v : V) (i : Fin (o.degree v)) :
    dist (portPoint T o v i) (d.point v) = r := by
  have hv : T.portVertex (o.darts ⟨v,i⟩) = v := o.darts_vertex ⟨v,i⟩
  simpa only [portPoint, hv] using T.port_distance (o.darts ⟨v,i⟩)

def point : PathCoreVertex o → Plane :=
  Sum.elim (fun q => portPoint T o q.1 q.2) (fun v => d.point v.1)

def curve : PathCoreEdge o → C(I, Plane) :=
  Sum.elim T.trimmedCurve (fun q =>
    straightCurve (portPoint T o q.1 (pathSource q.2)) (portPoint T o q.1 (pathTarget q.2)))

theorem pathCurve_mem_ball (v : V) (i : Fin (o.degree v - 1)) (t : I) :
    straightCurve (portPoint T o v (pathSource i)) (portPoint T o v (pathTarget i)) t ∈
      Metric.closedBall (d.point v) r := by
  apply (convex_closedBall _ _).segment_subset
    (show dist _ _ ≤ r from (portPoint_distance T o v (pathSource i)).le)
    (show dist _ _ ≤ r from (portPoint_distance T o v (pathTarget i)).le)
  exact straightCurve_mem_segment _ _ t

theorem point_injective : Function.Injective (point T o) := by
  rintro (⟨v,i⟩ | v) (⟨w,j⟩ | w) h
  · apply congrArg Sum.inl
    exact o.darts.injective (T.port_injective h)
  · exact (T.port_ne_point (o.darts ⟨v,i⟩) w.1 h).elim
  · exact (T.port_ne_point (o.darts ⟨w,j⟩) v.1 h.symm).elim
  · exact congrArg Sum.inr (Subtype.ext (d.point_injective h))

variable (hr0 : 0 < r)
  (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
  (a : ℝ)

include hr0 hr

-- The pointwise version avoids relying on composition notation at call sites.
theorem interior_injective
    (horder : ∀ v, StrictMono (fun i => linearProjection a (portPoint T o v i)))
    (e f : PathCoreEdge o) (s t : I) (hs : Inside s) (ht : Inside t)
    (h : curve T o e s = curve T o f t) : e = f ∧ s = t := by
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      obtain ⟨hef, hst⟩ := T.trimmedCurve_interior_injective e f s t h
      exact ⟨congrArg Sum.inl hef, hst⟩
    | inr f =>
      have hout := T.trimmedCurve_outside hr0 hr e s hs f.1
      have hin := pathCurve_mem_ball T o f.1 f.2 t
      change r < dist (curve T o (.inl e) s) (d.point f.1) at hout
      rw [h] at hout
      exact (not_lt_of_ge hin hout).elim
  | inr e =>
    cases f with
    | inl f =>
      have hout := T.trimmedCurve_outside hr0 hr f t ht e.1
      have hin := pathCurve_mem_ball T o e.1 e.2 s
      change r < dist (curve T o (.inl f) t) (d.point e.1) at hout
      rw [← h] at hout
      exact (not_lt_of_ge hin hout).elim
    | inr f =>
      rcases e with ⟨v,i⟩
      rcases f with ⟨w,j⟩
      by_cases hvw : v = w
      · subst w
        obtain ⟨hij, hst⟩ := path_curves_interior_injective (portPoint T o v) a
          (horder v) i j s t hs ht h
        exact ⟨congrArg Sum.inr (congrArg (Sigma.mk v) hij), hst⟩
      · have hd := d.radius_closedBalls_disjoint hr0 hr hvw
        exact (Set.disjoint_left.mp hd (pathCurve_mem_ball T o v i s)
          (h.symm ▸ pathCurve_mem_ball T o w j t)).elim

theorem interior_avoids
    (horder : ∀ v, StrictMono (fun i => linearProjection a (portPoint T o v i)))
    (e : PathCoreEdge o) (t : I) (ht : Inside t) (q : PathCoreVertex o) :
    curve T o e t ≠ point T o q := by
  intro h
  cases e with
  | inl e =>
    cases q with
    | inl q =>
      have hout := T.trimmedCurve_outside hr0 hr e t ht q.1
      change r < dist (curve T o (.inl e) t) (d.point q.1) at hout
      rw [h] at hout
      have hdist := portPoint_distance T o q.1 q.2
      change dist (point T o (.inl q)) (d.point q.1) = r at hdist
      rw [hdist] at hout
      exact (lt_irrefl r hout)
    | inr q =>
      have hout := T.trimmedCurve_outside hr0 hr e t ht q.1
      change r < dist (curve T o (.inl e) t) (d.point q.1) at hout
      rw [h] at hout
      change r < dist (d.point q.1) (d.point q.1) at hout
      simp only [dist_self] at hout
      exact (lt_asymm hr0 hout)
  | inr e =>
    rcases e with ⟨v,i⟩
    cases q with
    | inl q =>
      rcases q with ⟨w,j⟩
      by_cases hvw : v = w
      · subst w
        exact path_projection_avoids (portPoint T o v) a (horder v) i t ht j h
      · have hd := d.radius_closedBalls_disjoint hr0 hr hvw
        have hin : point T o (.inl ⟨w,j⟩) ∈ Metric.closedBall (d.point w) r :=
          (portPoint_distance T o w j).le
        exact Set.disjoint_left.mp hd (pathCurve_mem_ball T o v i t) (h.symm ▸ hin)
    | inr q =>
      have hvq : v ≠ q.1 := by
        intro hvq
        have hi := i.isLt
        simp [hvq, q.2] at hi
      have hd := d.radius_closedBalls_disjoint hr0 hr hvq
      have hin : point T o (.inr q) ∈ Metric.closedBall (d.point q.1) r :=
        Metric.mem_closedBall_self hr0.le
      exact Set.disjoint_left.mp hd (pathCurve_mem_ball T o v i t) (h.symm ▸ hin)

def drawing
    (horder : ∀ v, StrictMono (fun i => linearProjection a (portPoint T o v i))) :
    PlaneDrawing (pathCoreGraph o) where
  point := point T o
  point_injective := point_injective T o
  curve := curve T o
  curve_zero := by
    rintro (e | ⟨v,i⟩)
    · simp [curve, point, pathCoreGraph, portPoint]
    · exact straightCurve_zero _ _
  curve_one := by
    rintro (e | ⟨v,i⟩)
    · simp [curve, point, pathCoreGraph, portPoint]
    · exact straightCurve_one _ _
  interior_injective := interior_injective T o hr0 hr a horder
  interior_avoids := interior_avoids T o hr0 hr a horder

end PathCoreGeometry

theorem exists_planar_pathCore [Fintype V] [Fintype E] (hG : G.Planar) :
    ∃ o : G.IncidenceOrdering, (pathCoreGraph o).Planar := by
  obtain ⟨d⟩ := hG
  obtain ⟨r, hr0, hr⟩ := d.exists_vertex_radius
  let T := d.trimming hr0 hr
  obtain ⟨a, o, ho⟩ := exists_projected_incidenceOrdering T
  exact ⟨o, ⟨PathCoreGeometry.drawing T o hr0 hr a ho⟩⟩

end PlanarHom.Fisher
