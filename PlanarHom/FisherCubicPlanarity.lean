import PlanarHom.FisherTrianglePermutation
import PlanarHom.FisherTrimmedCurves
import PlanarHom.FisherCubicDecoration

/-! Actual ordinary planarity of the cubic Fisher triangle decoration. -/
noncomputable section
open Classical Set unitInterval

namespace PlanarHom.Fisher
open MultiGraph
variable {V E : Type*} (ports : (V × Fin 3) ≃ (E × Bool))

theorem cubic_dartVertex (q : E × Bool) :
    (cubicOriginal ports).dartVertex q = (ports.symm q).1 := by
  rcases q with ⟨e,b⟩
  cases b <;> rfl

namespace CubicGeometry
variable {ports} {d : PlaneDrawing (cubicOriginal ports)} {r : ℝ} (T : d.Trimming r)

def portPoint (v : V) (i : Fin 3) : Plane := T.port (ports (v,i))

theorem portPoint_injective (v : V) : Function.Injective (portPoint T v) := by
  intro i j h
  exact congrArg Prod.snd (ports.injective (T.port_injective h))

theorem portPoint_distance (v : V) (i : Fin 3) : dist (portPoint T v i) (d.point v) = r := by
  have hv : T.portVertex (ports (v,i)) = v := by
    change (cubicOriginal ports).dartVertex (ports (v,i)) = v
    rw [cubic_dartVertex, Equiv.symm_apply_apply]
  simpa only [portPoint, hv] using T.port_distance (ports (v,i))

def point (q : V × Fin 3) : Plane := portPoint T q.1 q.2

def curve (k : V → PlaneDrawing triangle) : E ⊕ (V × Fin 3) → C(I, Plane) :=
  Sum.elim T.trimmedCurve (fun q => (k q.1).curve q.2)

variable (hr0 : 0 < r)
  (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
  (k : V → PlaneDrawing triangle)
  (hk : ∀ v i, (k v).point i = portPoint T v i)
  (hball : ∀ v e t, (k v).curve e t ∈ Metric.closedBall (d.point v) r)

include hr0 hr hball

theorem interior_injective (e f : E ⊕ (V × Fin 3)) (s t : I)
    (hs : Inside s) (ht : Inside t) (h : curve T k e s = curve T k f t) : e = f ∧ s = t := by
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      obtain ⟨hef,hst⟩ := T.trimmedCurve_interior_injective e f s t h
      exact ⟨congrArg Sum.inl hef,hst⟩
    | inr f =>
      have hout := T.trimmedCurve_outside hr0 hr e s hs f.1
      change r < dist (curve T k (.inl e) s) (d.point f.1) at hout
      rw [h] at hout
      exact (not_lt_of_ge (hball f.1 f.2 t) hout).elim
  | inr e =>
    cases f with
    | inl f =>
      have hout := T.trimmedCurve_outside hr0 hr f t ht e.1
      change r < dist (curve T k (.inl f) t) (d.point e.1) at hout
      rw [← h] at hout
      exact (not_lt_of_ge (hball e.1 e.2 s) hout).elim
    | inr f =>
      rcases e with ⟨v,i⟩
      rcases f with ⟨w,j⟩
      by_cases hvw : v = w
      · subst w
        obtain ⟨hij,hst⟩ := (k v).interior_injective i j s t hs ht h
        exact ⟨congrArg Sum.inr (congrArg (Prod.mk v) hij),hst⟩
      · exact (Set.disjoint_left.mp (d.radius_closedBalls_disjoint hr0 hr hvw)
          (hball v i s) (h.symm ▸ hball w j t)).elim

include hk in
theorem interior_avoids (e : E ⊕ (V × Fin 3)) (t : I) (ht : Inside t) (q : V × Fin 3) :
    curve T k e t ≠ point T q := by
  intro h
  cases e with
  | inl e =>
    have hout := T.trimmedCurve_outside hr0 hr e t ht q.1
    change r < dist (curve T k (.inl e) t) (d.point q.1) at hout
    rw [h] at hout
    have hd := portPoint_distance T q.1 q.2
    change dist (point T q) (d.point q.1) = r at hd
    rw [hd] at hout
    exact lt_irrefl r hout
  | inr e =>
    rcases e with ⟨v,i⟩
    rcases q with ⟨w,j⟩
    by_cases hvw : v = w
    · subst w
      apply (k v).interior_avoids i t ht j
      exact h.trans (hk v j).symm
    · have hp : point T (w,j) ∈ Metric.closedBall (d.point w) r := (portPoint_distance T w j).le
      exact Set.disjoint_left.mp (d.radius_closedBalls_disjoint hr0 hr hvw)
        (hball v i t) (h.symm ▸ hp)

def drawing : PlaneDrawing (cubicDecoration ports) where
  point := point T
  point_injective := fun _ _ h => ports.injective (T.port_injective h)
  curve := curve T k
  curve_zero := by
    rintro (e | ⟨v,i⟩)
    · simp [curve, point, portPoint, cubicDecoration]
    · exact ((k v).curve_zero i).trans (hk v (triangle.src i))
  curve_one := by
    rintro (e | ⟨v,i⟩)
    · simp [curve, point, portPoint, cubicDecoration]
    · exact ((k v).curve_one i).trans (hk v (triangle.dst i))
  interior_injective := interior_injective T hr0 hr k hball
  interior_avoids := interior_avoids T hr0 hr k hk hball

end CubicGeometry

/-- Every finite ordinary planar cubic input has an actual planar Fisher
triangle decoration, for every incidence-port labeling. -/
theorem cubicDecoration_planar [Fintype V] [Fintype E]
    (h : (cubicOriginal ports).Planar) : (cubicDecoration ports).Planar := by
  obtain ⟨d⟩ := h
  obtain ⟨r,hr0,hr⟩ := d.exists_vertex_radius
  let T := d.trimming hr0 hr
  have hex (v : V) : ∃ k : PlaneDrawing triangle,
      (∀ i, k.point i = CubicGeometry.portPoint T v i) ∧
        ∀ e t, k.curve e t ∈ Metric.closedBall (d.point v) r :=
    exists_triangleDrawing_at_ports (CubicGeometry.portPoint T v)
      (CubicGeometry.portPoint_injective T v) (d.point v) r hr0
      (CubicGeometry.portPoint_distance T v)
  choose k hk hball using hex
  exact ⟨CubicGeometry.drawing T hr0 hr k hk hball⟩

end PlanarHom.Fisher
