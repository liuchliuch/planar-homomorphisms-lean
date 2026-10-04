import PlanarHom.FisherOrderedTriangle
import PlanarHom.PlanarTransport

/-! Transporting the local triangle drawing through arbitrary port labels. -/
noncomputable section
open Classical Set unitInterval

namespace PlanarHom.MultiGraph.PlaneDrawing

def reverseTime : C(I, I) where
  toFun t := ⟨1-(t:ℝ), by constructor <;> linarith [t.2.1,t.2.2]⟩
  continuous_toFun := by fun_prop

def orientedTime (b : Bool) : C(I,I) := if b then reverseTime else ContinuousMap.id I

theorem orientedTime_inside (b : Bool) (t : I) (ht : Inside t) : Inside (orientedTime b t) := by
  cases b
  · exact ht
  · change 0 < 1-(t:ℝ) ∧ 1-(t:ℝ) < 1
    constructor <;> linarith [ht.1,ht.2]

theorem orientedTime_injective (b : Bool) : Function.Injective (orientedTime b) := by
  cases b
  · exact Function.injective_id
  · intro s t h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change 1-(s:ℝ) = 1-(t:ℝ) at hh
    linarith

variable {V E : Type*} {G H : MultiGraph V E}

def reorient (d : PlaneDrawing G) (b : E → Bool)
    (hs : ∀ e, H.src e = if b e then G.dst e else G.src e)
    (ht : ∀ e, H.dst e = if b e then G.src e else G.dst e) : PlaneDrawing H where
  point := d.point
  point_injective := d.point_injective
  curve e := (d.curve e).comp (orientedTime (b e))
  curve_zero := by
    intro e
    cases he : b e <;>
      simp [orientedTime, reverseTime, he, hs, d.curve_zero, d.curve_one]
  curve_one := by
    intro e
    cases he : b e <;>
      simp [orientedTime, reverseTime, he, ht, d.curve_zero, d.curve_one]
  interior_injective := by
    intro e f s t hs' ht' h
    obtain ⟨hef,hst⟩ := d.interior_injective e f _ _
      (orientedTime_inside (b e) s hs') (orientedTime_inside (b f) t ht') h
    subst f
    exact ⟨rfl, orientedTime_injective (b e) hst⟩
  interior_avoids e t ht' v := d.interior_avoids e _ (orientedTime_inside (b e) t ht') v

end PlanarHom.MultiGraph.PlaneDrawing

namespace PlanarHom.Fisher
open MultiGraph

theorem triangle_distinct_endpoints : ∀ i : Fin 3, triangle.src i ≠ triangle.dst i := by
  decide +kernel

theorem triangle_endpoint_ne_opposite :
    ∀ i : Fin 3, triangle.src i ≠ i ∧ triangle.dst i ≠ i := by
  decide +kernel

theorem triangle_other_pair : ∀ i u v : Fin 3, u ≠ i → v ≠ i → u ≠ v →
    ((u = triangle.src i ∧ v = triangle.dst i) ∨
      (u = triangle.dst i ∧ v = triangle.src i)) := by
  decide +kernel

def triangleRelabel (perm : Fin 3 ≃ Fin 3) := triangle.reindex perm perm

theorem triangleRelabel_endpoints (perm : Fin 3 ≃ Fin 3) (i : Fin 3) :
    (((triangleRelabel perm).src i = triangle.src i ∧ (triangleRelabel perm).dst i = triangle.dst i) ∨
      ((triangleRelabel perm).src i = triangle.dst i ∧ (triangleRelabel perm).dst i = triangle.src i)) := by
  apply triangle_other_pair
  · change perm (triangle.src (perm.symm i)) ≠ i
    simpa only [Equiv.apply_symm_apply] using
      perm.injective.ne (triangle_endpoint_ne_opposite (perm.symm i)).1
  · change perm (triangle.dst (perm.symm i)) ≠ i
    simpa only [Equiv.apply_symm_apply] using
      perm.injective.ne (triangle_endpoint_ne_opposite (perm.symm i)).2
  · exact perm.injective.ne (triangle_distinct_endpoints (perm.symm i))

def triangleFlip (perm : Fin 3 ≃ Fin 3) (i : Fin 3) : Bool :=
  decide ((triangleRelabel perm).src i ≠ triangle.src i)

theorem triangleFlip_endpoints (perm : Fin 3 ≃ Fin 3) (i : Fin 3) :
    (triangle.src i = if triangleFlip perm i then (triangleRelabel perm).dst i else (triangleRelabel perm).src i) ∧
    (triangle.dst i = if triangleFlip perm i then (triangleRelabel perm).src i else (triangleRelabel perm).dst i) := by
  rcases triangleRelabel_endpoints perm i with h | h
  · simp [triangleFlip,h.1,h.2]
  · simp [triangleFlip,h.1,h.2,(triangle_distinct_endpoints i).symm]

/-- Port relabeling changes only edge parametrization direction, when needed. -/
def relabelTriangleDrawing (perm : Fin 3 ≃ Fin 3) (d : PlaneDrawing triangle) : PlaneDrawing triangle :=
  (d.transport (triangle.reindexEquiv perm perm)).reorient (triangleFlip perm)
    (fun i => (triangleFlip_endpoints perm i).1) (fun i => (triangleFlip_endpoints perm i).2)

@[simp] theorem relabelTriangleDrawing_point (perm : Fin 3 ≃ Fin 3) (d : PlaneDrawing triangle)
    (i : Fin 3) : (relabelTriangleDrawing perm d).point i = d.point (perm.symm i) := rfl

def orderedTripleEnum {T : Type*} [Fintype T] (f : T → ℝ) (hf : Function.Injective f)
    (hc : Fintype.card T = 3) : Fin 3 ≃ T := by
  letI : LinearOrder T := LinearOrder.lift' f hf
  exact (Fintype.orderIsoFinOfCardEq T hc).toEquiv

theorem orderedTripleEnum_mono {T : Type*} [Fintype T] (f : T → ℝ) (hf : Function.Injective f)
    (hc : Fintype.card T = 3) : StrictMono (fun i => f (orderedTripleEnum f hf hc i)) := by
  letI : LinearOrder T := LinearOrder.lift' f hf
  exact (Fintype.orderIsoFinOfCardEq T hc).strictMono

/-- Every injective triple of ports on an actual vertex sphere admits a
triangle drawing with exactly those port positions, inside that same ball. -/
theorem exists_triangleDrawing_at_ports (p : Fin 3 → Plane) (hp : Function.Injective p)
    (c : Plane) (r : ℝ) (hr : 0 < r) (hsphere : ∀ i, dist (p i) c = r) :
    ∃ d : PlaneDrawing triangle, (∀ i, d.point i = p i) ∧
      ∀ e t, d.curve e t ∈ Metric.closedBall c r := by
  obtain ⟨a,ha⟩ := exists_injective_linearProjection p hp
  let perm : Fin 3 ≃ Fin 3 := orderedTripleEnum (fun i => linearProjection a (p i)) ha (by simp)
  have hmono : StrictMono (fun i => linearProjection a (p (perm i))) :=
    orderedTripleEnum_mono (fun i => linearProjection a (p i)) ha (by simp)
  let d := orderedTriangleDrawing (fun i => p (perm i)) c r a hr (fun i => hsphere (perm i)) hmono
  refine ⟨relabelTriangleDrawing perm d, ?_, ?_⟩
  · intro i
    simp [d, orderedTriangleDrawing]
  · intro e t
    exact orderedTriangle_curve_mem_ball (fun i => p (perm i)) c r hr
      (fun i => hsphere (perm i)) (perm.symm e) (PlaneDrawing.orientedTime (triangleFlip perm e) t)

end PlanarHom.Fisher
