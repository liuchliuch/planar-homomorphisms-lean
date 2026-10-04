import PlanarHom.PlanarTruncation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Straight radial half-edge tails

Distinct ports on a common vertex sphere determine radial segments meeting only
at their center. Together with the proved trimming inequalities this separates
each compact middle arc from every other occurrence's radial tails. The arguments
use norm homogeneity and apply to the actual product-plane norm.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.MultiGraph

/-- The only point of a radial segment reaching the endpoint radius is the endpoint. -/
theorem radial_boundary_unique {c p x : Plane} {r : ℝ} (hr : 0 < r)
    (hp : dist p c = r) (hx : x ∈ [c -[ℝ] p]) (hrx : r ≤ dist x c) : x = p := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨s,hs,rfl⟩ := hx
  rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hs.1, dist_comm c p, hp] at hrx
  have hs1 : s = 1 := by nlinarith [hs.2]
  simp [hs1]

/-- Distinct points of one sphere yield radial segments intersecting only at the center. -/
theorem radial_intersection {c p q x : Plane} {r : ℝ} (hr : 0 < r)
    (hp : dist p c = r) (hq : dist q c = r) (hpq : p ≠ q)
    (hxp : x ∈ [c -[ℝ] p]) (hxq : x ∈ [c -[ℝ] q]) : x = c := by
  rw [segment_eq_image_lineMap] at hxp hxq
  obtain ⟨s,hs,rfl⟩ := hxp
  obtain ⟨t,ht,heq⟩ := hxq
  have hd := congrArg (fun x => dist x c) heq
  simp only [dist_lineMap_left, Real.norm_eq_abs,
    abs_of_nonneg hs.1,abs_of_nonneg ht.1,dist_comm c p,dist_comm c q,hp,hq] at hd
  have hst : t = s := by nlinarith
  subst t
  by_cases hs0 : s = 0
  · simp [hs0]
  · exfalso
    apply hpq
    have heq' : s • q = s • p := by
      simpa only [AffineMap.lineMap_apply_module, add_right_inj] using heq
    exact (smul_right_injective Plane hs0 heq').symm

namespace PlaneDrawing.Trimming
variable {V E : Type*} {G : MultiGraph V E} {d : PlaneDrawing G} {r : ℝ}
variable (T : d.Trimming r)

/-- Incidence vertex of one of an occurrence's two half-edges. -/
def portVertex (_T : d.Trimming r) (p : E × Bool) : V := if p.2 then G.dst p.1 else G.src p.1

theorem port_distance (p : E × Bool) : dist (T.port p) (d.point (T.portVertex p)) = r := by
  rcases p with ⟨e,b⟩
  cases b
  · exact T.left_sphere e
  · exact T.right_sphere e

/-- Straight radial segment of a half-edge, including its incident vertex. -/
def radial (p : E × Bool) : Set Plane := [d.point (T.portVertex p) -[ℝ] T.port p]

theorem isCompact_radial (p : E × Bool) : IsCompact (T.radial p) := by
  rw [radial,segment_eq_image_lineMap]
  exact isCompact_Icc.image (by fun_prop)

theorem radial_subset_closedBall (hr : 0 < r) (p : E × Bool) :
    T.radial p ⊆ Metric.closedBall (d.point (T.portVertex p)) r :=
  (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self hr.le)
    (T.port_distance p).le

/-- Distinct radial half-edges meet only at an incident vertex common to both. -/
theorem radial_intersection_vertex (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {p q : E × Bool} (hpq : p ≠ q) {x : Plane}
    (hxp : x ∈ T.radial p) (hxq : x ∈ T.radial q) :
    T.portVertex p = T.portVertex q ∧ x = d.point (T.portVertex p) := by
  by_cases hv : T.portVertex p = T.portVertex q
  · refine ⟨hv,?_⟩
    apply radial_intersection hr0 (T.port_distance p)
      (show dist (T.port q) (d.point (T.portVertex p)) = r by rw [hv,T.port_distance])
      (T.port_injective.ne hpq) hxp
    simpa only [radial,hv] using hxq
  · exact False.elim ((Set.disjoint_left.mp (d.radius_closedBalls_disjoint hr0 hr hv))
      (T.radial_subset_closedBall hr0 p hxp) (T.radial_subset_closedBall hr0 q hxq))

theorem port_mem_middle (p : E × Bool) : T.port p ∈ T.middle p.1 := by
  rcases p with ⟨e,b⟩
  cases b
  · exact ⟨T.left e,⟨le_rfl,(T.left_lt_right e).le⟩,rfl⟩
  · exact ⟨T.right e,⟨(T.left_lt_right e).le,le_rfl⟩,rfl⟩

/-- A middle arc meets radial tails only at its own two prescribed ports. -/
theorem middle_radial_intersection (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {e : E} {p : E × Bool} {x : Plane} (hxe : x ∈ T.middle e) (hxp : x ∈ T.radial p) :
    e = p.1 ∧ x = T.port p := by
  obtain ⟨t,ht,rfl⟩ := hxe
  have hxport : d.curve e t = T.port p := radial_boundary_unique hr0 (T.port_distance p)
    hxp (T.middle_outside hr0 hr e t ht (T.portVertex p))
  refine ⟨?_,hxport⟩
  have hm : d.curve e t ∈ T.middle p.1 := hxport ▸ T.port_mem_middle p
  by_contra he
  exact Set.disjoint_left.mp (T.middle_disjoint he) ⟨t,ht,rfl⟩ hm

/-- Hence each middle arc is disjoint from every other edge occurrence's radial tail. -/
theorem middle_disjoint_other_radial (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {e : E} {p : E × Bool} (he : e ≠ p.1) : Disjoint (T.middle e) (T.radial p) := by
  apply Set.disjoint_left.mpr
  intro x hx hp
  exact he (T.middle_radial_intersection hr0 hr hx hp).1

/-- The middle arcs avoid all original vertex positions. -/
theorem point_notMem_middle (e : E) (v : V) : d.point v ∉ T.middle e := by
  rintro ⟨t,ht,h⟩
  exact d.interior_avoids e t (T.middle_inside e ht) v h

end PlaneDrawing.Trimming
end PlanarHom.MultiGraph
