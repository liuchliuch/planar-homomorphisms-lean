import PlanarHom.PlanarEmbedding
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact separation around the vertices of a finite ordinary drawing

This is an elementary step toward redrawing an arbitrary finite plane embedding
with polygonal edges. A positive uniform radius is obtained from the given
continuous drawing itself. Every vertex ball excludes all nonincident edge
pieces, all middle thirds, and all other vertices. No regular-neighborhood or
polygonal-redrawing conclusion is assumed.
-/

noncomputable section
open Set unitInterval
open Classical
namespace PlanarHom.MultiGraph
namespace PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- An interval parameter away from both endpoints is strictly interior. -/
theorem inside_of_ne_endpoints {t : I} (h0 : t ≠ 0) (h1 : t ≠ 1) : Inside t := by
  constructor
  · exact lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm))
  · exact lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))

/-- All edge/vertex collisions in an ordinary drawing are prescribed endpoints. -/
theorem curve_eq_point_iff (d : PlaneDrawing G) (e : E) (t : I) (v : V) :
    d.curve e t = d.point v ↔
      (t = 0 ∧ G.src e = v) ∨ (t = 1 ∧ G.dst e = v) := by
  constructor
  · intro h
    by_cases h0 : t = 0
    · left
      exact ⟨h0,d.point_injective (by simpa [h0, d.curve_zero] using h)⟩
    · by_cases h1 : t = 1
      · right
        exact ⟨h1,d.point_injective (by simpa [h1, d.curve_one] using h)⟩
      · exact False.elim (d.interior_avoids e t (inside_of_ne_endpoints h0 h1) v h)
  · rintro (⟨rfl,h⟩ | ⟨rfl,h⟩)
    · simpa [h] using d.curve_zero e
    · simpa [h] using d.curve_one e

/-- The support is compact for finite graphs, even with loops and isolated vertices. -/
theorem isCompact_support [Finite V] [Finite E] (d : PlaneDrawing G) :
    IsCompact d.support :=
  (Set.finite_range d.point).isCompact.union
    (isCompact_iUnion (fun e => isCompact_range (d.curve e).continuous))

/-- First fixed cut separating a short initial parameter interval. -/
def firstThird : I := ⟨1/3, by constructor <;> norm_num⟩
/-- Second fixed cut separating a short final parameter interval. -/
def secondThird : I := ⟨2/3, by constructor <;> norm_num⟩

@[simp] theorem firstThird_inside : Inside firstThird := by norm_num [Inside, firstThird]
@[simp] theorem secondThird_inside : Inside secondThird := by norm_num [Inside, secondThird]
theorem firstThird_lt_secondThird : firstThird < secondThird := by
  change (1/3 : ℝ) < 2/3
  norm_num

/-- Remove a source tail only when that source is the vertex under consideration. -/
def portLo (G : MultiGraph V E) (v : V) (e : E) : I :=
  if G.src e = v then firstThird else 0

/-- Remove a destination tail only when that destination is the given vertex. -/
def portHi (G : MultiGraph V E) (v : V) (e : E) : I :=
  if G.dst e = v then secondThird else 1

theorem portLo_le_firstThird (v : V) (e : E) : portLo G v e ≤ firstThird := by
  unfold portLo
  split
  · exact le_rfl
  · change (0 : ℝ) ≤ 1/3
    norm_num

theorem secondThird_le_portHi (v : V) (e : E) : secondThird ≤ portHi G v e := by
  unfold portHi
  split
  · exact le_rfl
  · change (2/3 : ℝ) ≤ 1
    norm_num

/-- Compact drawing pieces which must remain outside a vertex neighborhood. -/
def forbidden (d : PlaneDrawing G) (v : V) : Set Plane :=
  (d.point '' {w | w ≠ v}) ∪
    ⋃ e, d.curve e '' Set.Icc (portLo G v e) (portHi G v e)

theorem isCompact_forbidden [Finite V] [Finite E] (d : PlaneDrawing G) (v : V) :
    IsCompact (d.forbidden v) :=
  ((Set.toFinite _).image d.point).isCompact.union
    (isCompact_iUnion (fun e => isCompact_Icc.image (d.curve e).continuous))

theorem point_notMem_forbidden (d : PlaneDrawing G) (v : V) :
    d.point v ∉ d.forbidden v := by
  rintro (⟨w,hw,heq⟩ | h)
  · exact hw (d.point_injective heq)
  · obtain ⟨e,t,ht,heq⟩ := Set.mem_iUnion.mp h
    rcases (d.curve_eq_point_iff e t v).mp heq with ⟨h0,hs⟩ | ⟨h1,hd⟩
    · have ht' := ht.1
      rw [portLo, if_pos hs, h0] at ht'
      change (1/3 : ℝ) ≤ 0 at ht'
      norm_num at ht'
    · have ht' := ht.2
      rw [portHi, if_pos hd, h1] at ht'
      change (1 : ℝ) ≤ 2/3 at ht'
      norm_num at ht'

/-- A positive function on a finite type has a positive uniform lower bound,
including when the type is empty. -/
theorem finite_positive_lower_bound {A : Type*} [Finite A] (f : A → ℝ)
    (hf : ∀ a, 0 < f a) : ∃ ε > 0, ∀ a, ε ≤ f a := by
  letI := Fintype.ofFinite A
  suffices ∀ s : Finset A, ∃ ε > 0, ∀ a ∈ s, ε ≤ f a by
    obtain ⟨ε,hε,hall⟩ := this Finset.univ
    exact ⟨ε,hε,fun a => hall a (Finset.mem_univ a)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨ε,hε,hs⟩ := ih
    refine ⟨min (f a) ε, lt_min (hf a) hε, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hs b hb)

/-- Actual uniform metric separation, proved solely from finite ordinary
plane-drawing data and compactness. The factor four reserves room for later
truncation, radial tails and polygonal perturbation. -/
theorem exists_vertex_radius [Finite V] [Finite E] (d : PlaneDrawing G) :
    ∃ r : ℝ, 0 < r ∧ ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v) := by
  have hlocal : ∀ v, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (d.point v) ε ⊆ (d.forbidden v)ᶜ := by
    intro v
    exact Metric.isOpen_iff.mp (d.isCompact_forbidden v).isClosed.isOpen_compl
      (d.point v) (d.point_notMem_forbidden v)
  choose ε hε hball using hlocal
  obtain ⟨δ,hδ,hδε⟩ := finite_positive_lower_bound ε hε
  refine ⟨δ/8, by positivity, ?_⟩
  intro v p hp
  have hd : ε v ≤ dist p (d.point v) := by
    by_contra h
    exact hball v (lt_of_not_ge h) hp
  have hv := hδε v
  linarith

/-- Distinct vertex centers are separated by the same uniform margin. -/
theorem radius_vertex_separation (d : PlaneDrawing G) {r : ℝ}
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {v w : V} (hvw : v ≠ w) : 4*r < dist (d.point v) (d.point w) :=
  hr w (d.point v) (Or.inl ⟨v,hvw,rfl⟩)

/-- In particular, closed vertex balls of radius `r` are pairwise disjoint. -/
theorem radius_closedBalls_disjoint (d : PlaneDrawing G) {r : ℝ} (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    {v w : V} (hvw : v ≠ w) :
    Disjoint (Metric.closedBall (d.point v) r) (Metric.closedBall (d.point w) r) := by
  apply Set.disjoint_left.mpr
  intro p hpv hpw
  have hsep := d.radius_vertex_separation hr hvw
  have htri := dist_triangle (d.point v) p (d.point w)
  have hv : dist (d.point v) p ≤ r := by simpa only [dist_comm] using hpv
  have hw : dist p (d.point w) ≤ r := hpw
  linarith

/-- Every middle-third point lies well outside every vertex ball. -/
theorem radius_middle_separation (d : PlaneDrawing G) {r : ℝ}
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    (e : E) (t : I) (ht : t ∈ Set.Icc firstThird secondThird) (v : V) :
    4*r < dist (d.curve e t) (d.point v) := by
  apply hr v _
  right
  apply Set.mem_iUnion.mpr
  refine ⟨e,t,?_,rfl⟩
  exact ⟨(portLo_le_firstThird v e).trans ht.1, ht.2.trans (secondThird_le_portHi v e)⟩

end PlaneDrawing
end PlanarHom.MultiGraph
