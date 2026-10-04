import PlanarHom.PlanarRadialTails

/-!
# Trimming with vertex-dependent radii

Each vertex has its own positive radius. The separation margin gives disjoint
vertex balls, last/first sphere ports, compact connected middle arcs, and the
same radial-tail separation properties as uniform-radius trimming.
-/

noncomputable section
open Set unitInterval
open scoped Convex
namespace PlanarHom.MultiGraph
namespace PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- Distinct vertex centers are separated by the radius assigned to either center. -/
theorem variable_radius_vertex_separation (d : PlaneDrawing G) {rho : V → ℝ}
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v))
    {v w : V} (hvw : v ≠ w) : 4*rho w < dist (d.point v) (d.point w) :=
  hr w (d.point v) (Or.inl ⟨v,hvw,rfl⟩)

/-- Closed balls with the separately chosen radii are pairwise disjoint. -/
theorem variable_radius_closedBalls_disjoint (d : PlaneDrawing G) {rho : V → ℝ}
    (hr0 : ∀ v, 0 < rho v)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v))
    {v w : V} (hvw : v ≠ w) :
    Disjoint (Metric.closedBall (d.point v) (rho v))
      (Metric.closedBall (d.point w) (rho w)) := by
  apply Set.disjoint_left.mpr
  intro p hpv hpw
  have hsepw := d.variable_radius_vertex_separation hr hvw
  have hsepv := d.variable_radius_vertex_separation hr (Ne.symm hvw)
  rw [dist_comm (d.point w) (d.point v)] at hsepv
  have htri := dist_triangle (d.point v) p (d.point w)
  have hv : dist (d.point v) p ≤ rho v := by simpa only [dist_comm] using hpv
  have hw : dist p (d.point w) ≤ rho w := hpw
  linarith [hr0 v, hr0 w]

/-- Every middle-third point lies outside each separately chosen vertex ball. -/
theorem variable_radius_middle_separation (d : PlaneDrawing G) {rho : V → ℝ}
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v))
    (e : E) (t : I) (ht : t ∈ Set.Icc firstThird secondThird) (v : V) :
    4*rho v < dist (d.curve e t) (d.point v) := by
  apply hr v _
  right
  apply Set.mem_iUnion.mpr
  refine ⟨e,t,?_,rfl⟩
  exact ⟨(portLo_le_firstThird v e).trans ht.1, ht.2.trans (secondThird_le_portHi v e)⟩

/-- The two ports for each edge and verified one-sided distance inequalities. -/
structure VariableTrimming (d : PlaneDrawing G) (rho : V → ℝ) where
  left : E → I
  right : E → I
  left_bounds : ∀ e, left e ∈ Set.Ioo 0 firstThird
  right_bounds : ∀ e, right e ∈ Set.Ioo secondThird 1
  left_sphere : ∀ e, dist (d.curve e (left e)) (d.point (G.src e)) = rho (G.src e)
  right_sphere : ∀ e, dist (d.curve e (right e)) (d.point (G.dst e)) = rho (G.dst e)
  source_tail : ∀ e t, t ∈ Set.Ioc (left e) firstThird →
    rho (G.src e) < dist (d.curve e t) (d.point (G.src e))
  destination_tail : ∀ e t, t ∈ Set.Ico secondThird (right e) →
    rho (G.dst e) < dist (d.curve e t) (d.point (G.dst e))

/-- Construct ports from vertex-dependent radii and their separation margins. -/
def variableTrimming (d : PlaneDrawing G) {rho : V → ℝ} (hr0 : ∀ v, 0 < rho v)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v)) : VariableTrimming d rho := by
  have hleft : ∀ e, ∃ s ∈ Set.Ioo (0 : I) firstThird,
      dist (d.curve e s) (d.point (G.src e)) = rho (G.src e) ∧
      ∀ t ∈ Set.Ioc s firstThird, rho (G.src e) < dist (d.curve e t) (d.point (G.src e)) := by
    intro e
    let f : C(I,ℝ) := ⟨fun t => dist (d.curve e t) (d.point (G.src e)), by fun_prop⟩
    apply last_level_crossing f (show (0 : I) ≤ firstThird from bot_le)
    · simpa [f,d.curve_zero] using hr0 (G.src e)
    · have h := d.variable_radius_middle_separation hr e firstThird
        ⟨le_rfl,firstThird_lt_secondThird.le⟩ (G.src e)
      dsimp [f]
      linarith [hr0 (G.src e)]
  have hright : ∀ e, ∃ s ∈ Set.Ioo secondThird (1 : I),
      dist (d.curve e s) (d.point (G.dst e)) = rho (G.dst e) ∧
      ∀ t ∈ Set.Ico secondThird s, rho (G.dst e) < dist (d.curve e t) (d.point (G.dst e)) := by
    intro e
    let f : C(I,ℝ) := ⟨fun t => dist (d.curve e t) (d.point (G.dst e)), by fun_prop⟩
    apply first_level_crossing f (show secondThird ≤ (1 : I) from le_top)
    · have h := d.variable_radius_middle_separation hr e secondThird
        ⟨firstThird_lt_secondThird.le,le_rfl⟩ (G.dst e)
      dsimp [f]
      linarith [hr0 (G.dst e)]
    · simpa [f,d.curve_one] using hr0 (G.dst e)
  choose left hl hs htail using hleft
  choose right hr' ht htail' using hright
  exact ⟨left,right,hl,hr',hs,ht,htail,htail'⟩

namespace VariableTrimming
variable {d : PlaneDrawing G} {rho : V → ℝ} (T : VariableTrimming d rho)

theorem left_lt_right (e : E) : T.left e < T.right e :=
  (T.left_bounds e).2.trans (firstThird_lt_secondThird.trans (T.right_bounds e).1)

theorem left_inside (e : E) : Inside (T.left e) :=
  ⟨(T.left_bounds e).1, ((T.left_bounds e).2.trans
    (firstThird_lt_secondThird.trans (T.right_bounds e).1)).trans (T.right_bounds e).2⟩

theorem right_inside (e : E) : Inside (T.right e) :=
  ⟨(T.left_bounds e).1.trans (T.left_lt_right e),(T.right_bounds e).2⟩

theorem middle_inside (e : E) {t : I} (ht : t ∈ Set.Icc (T.left e) (T.right e)) : Inside t :=
  ⟨(T.left_inside e).1.trans_le ht.1,
    lt_of_le_of_lt (show (t : ℝ) ≤ (T.right e : ℝ) from ht.2) (T.right_inside e).2⟩

/-- Open trimmed edge interiors avoid every closed vertex ball. -/
theorem middle_strictly_outside (hr0 : ∀ v, 0 < rho v)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v))
    (e : E) (t : I) (ht : t ∈ Set.Ioo (T.left e) (T.right e)) (v : V) :
    rho v < dist (d.curve e t) (d.point v) := by
  by_cases ha : t ≤ firstThird
  · by_cases hv : G.src e = v
    · simpa [hv] using T.source_tail e t ⟨ht.1,ha⟩
    · have h := hr v (d.curve e t) (Or.inr (Set.mem_iUnion.mpr
        ⟨e,t,⟨by simp [portLo,hv], ha.trans
          (firstThird_lt_secondThird.le.trans (secondThird_le_portHi v e))⟩,rfl⟩))
      linarith [hr0 v]
  · by_cases hb : t ≤ secondThird
    · have h := d.variable_radius_middle_separation hr e t ⟨(lt_of_not_ge ha).le,hb⟩ v
      linarith [hr0 v]
    · by_cases hv : G.dst e = v
      · simpa [hv] using T.destination_tail e t ⟨(lt_of_not_ge hb).le,ht.2⟩
      · have h := hr v (d.curve e t) (Or.inr (Set.mem_iUnion.mpr
          ⟨e,t,⟨(portLo_le_firstThird v e).trans (lt_of_not_ge ha).le,
            by simp only [portHi,if_neg hv]; exact le_top⟩,rfl⟩))
        linarith [hr0 v]

/-- Closed trimmed arcs stay outside open vertex balls, with possible equality
only at their own source/destination ports. -/
theorem middle_outside (hr0 : ∀ v, 0 < rho v)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v))
    (e : E) (t : I) (ht : t ∈ Set.Icc (T.left e) (T.right e)) (v : V) :
    rho v ≤ dist (d.curve e t) (d.point v) := by
  by_cases hl : t = T.left e
  · subst t
    by_cases hv : G.src e = v
    · simpa [hv] using (T.left_sphere e).ge
    · have h := hr v (d.curve e (T.left e)) (Or.inr (Set.mem_iUnion.mpr
        ⟨e,T.left e,⟨by simp [portLo,hv], (T.left_bounds e).2.le.trans
          (firstThird_lt_secondThird.le.trans (secondThird_le_portHi v e))⟩,rfl⟩))
      linarith [hr0 v]
  · by_cases hr' : t = T.right e
    · subst t
      by_cases hv : G.dst e = v
      · simpa [hv] using (T.right_sphere e).ge
      · have h := hr v (d.curve e (T.right e)) (Or.inr (Set.mem_iUnion.mpr
          ⟨e,T.right e,⟨(portLo_le_firstThird v e).trans
            (firstThird_lt_secondThird.le.trans (T.right_bounds e).1.le),
            by simp only [portHi,if_neg hv]; exact le_top⟩,rfl⟩))
        linarith [hr0 v]
    · exact (T.middle_strictly_outside hr0 hr e t
        ⟨lt_of_le_of_ne ht.1 (Ne.symm hl),lt_of_le_of_ne ht.2 hr'⟩ v).le

/-- The actual compact image of a trimmed occurrence. -/
def middle (e : E) : Set Plane := d.curve e '' Set.Icc (T.left e) (T.right e)

theorem isCompact_middle (e : E) : IsCompact (T.middle e) :=
  isCompact_Icc.image (d.curve e).continuous

theorem isConnected_middle (e : E) : IsConnected (T.middle e) :=
  (isConnected_Icc (T.left_lt_right e).le).image _ (d.curve e).continuous.continuousOn

/-- Different occurrences retain disjoint compact middle arcs. -/
theorem middle_disjoint {e f : E} (hef : e ≠ f) : Disjoint (T.middle e) (T.middle f) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨s,hs,he⟩ ⟨t,ht,hf⟩
  exact hef (d.interior_injective e f s t (T.middle_inside e hs) (T.middle_inside f ht)
    (he.trans hf.symm)).1

/-- Every loop contributes two distinct half-edge port positions. -/
def port (p : E × Bool) : Plane :=
  d.curve p.1 (if p.2 then T.right p.1 else T.left p.1)

theorem port_injective : Function.Injective T.port := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have hi (g : E) (b : Bool) : Inside (if b then T.right g else T.left g) := by
    cases b
    · exact T.left_inside g
    · exact T.right_inside g
  obtain ⟨hef,hst⟩ := d.interior_injective e f _ _ (hi e b) (hi f c) h
  subst f
  cases b <;> cases c
  · rfl
  · exact False.elim ((T.left_lt_right e).ne hst)
  · exact False.elim ((T.left_lt_right e).ne hst.symm)
  · rfl

end VariableTrimming
end PlaneDrawing

namespace PlaneDrawing.VariableTrimming
variable {V E : Type*} {G : MultiGraph V E} {d : PlaneDrawing G} {rho : V → ℝ}
variable (T : d.VariableTrimming rho)

/-- Incidence vertex of one of an occurrence's two half-edges. -/
def portVertex (_T : d.VariableTrimming rho) (p : E × Bool) : V := if p.2 then G.dst p.1 else G.src p.1

theorem port_distance (p : E × Bool) : dist (T.port p) (d.point (T.portVertex p)) = rho (T.portVertex p) := by
  rcases p with ⟨e,b⟩
  cases b
  · exact T.left_sphere e
  · exact T.right_sphere e

/-- Straight radial segment of a half-edge, including its incident vertex. -/
def radial (p : E × Bool) : Set Plane := [d.point (T.portVertex p) -[ℝ] T.port p]

theorem isCompact_radial (p : E × Bool) : IsCompact (T.radial p) := by
  rw [radial,segment_eq_image_lineMap]
  exact isCompact_Icc.image (by fun_prop)

theorem radial_subset_closedBall (hr : ∀ v, 0 < rho v) (p : E × Bool) :
    T.radial p ⊆ Metric.closedBall (d.point (T.portVertex p)) (rho (T.portVertex p)) :=
  (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self (hr (T.portVertex p)).le)
    (T.port_distance p).le

/-- Distinct radial half-edges meet only at an incident vertex common to both. -/
theorem radial_intersection_vertex (hr0 : ∀ v, 0 < rho v)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v))
    {p q : E × Bool} (hpq : p ≠ q) {x : Plane}
    (hxp : x ∈ T.radial p) (hxq : x ∈ T.radial q) :
    T.portVertex p = T.portVertex q ∧ x = d.point (T.portVertex p) := by
  by_cases hv : T.portVertex p = T.portVertex q
  · refine ⟨hv,?_⟩
    apply radial_intersection (hr0 (T.portVertex p)) (T.port_distance p)
      (show dist (T.port q) (d.point (T.portVertex p)) = rho (T.portVertex p) by rw [hv,T.port_distance])
      (T.port_injective.ne hpq) hxp
    simpa only [radial,hv] using hxq
  · exact False.elim ((Set.disjoint_left.mp (d.variable_radius_closedBalls_disjoint hr0 hr hv))
      (T.radial_subset_closedBall hr0 p hxp) (T.radial_subset_closedBall hr0 q hxq))

theorem port_mem_middle (p : E × Bool) : T.port p ∈ T.middle p.1 := by
  rcases p with ⟨e,b⟩
  cases b
  · exact ⟨T.left e,⟨le_rfl,(T.left_lt_right e).le⟩,rfl⟩
  · exact ⟨T.right e,⟨(T.left_lt_right e).le,le_rfl⟩,rfl⟩

/-- A middle arc meets radial tails only at its own two prescribed ports. -/
theorem middle_radial_intersection (hr0 : ∀ v, 0 < rho v)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v))
    {e : E} {p : E × Bool} {x : Plane} (hxe : x ∈ T.middle e) (hxp : x ∈ T.radial p) :
    e = p.1 ∧ x = T.port p := by
  obtain ⟨t,ht,rfl⟩ := hxe
  have hxport : d.curve e t = T.port p := radial_boundary_unique (hr0 (T.portVertex p)) (T.port_distance p)
    hxp (T.middle_outside hr0 hr e t ht (T.portVertex p))
  refine ⟨?_,hxport⟩
  have hm : d.curve e t ∈ T.middle p.1 := hxport ▸ T.port_mem_middle p
  by_contra he
  exact Set.disjoint_left.mp (T.middle_disjoint he) ⟨t,ht,rfl⟩ hm

/-- Hence each middle arc is disjoint from every other edge occurrence's radial tail. -/
theorem middle_disjoint_other_radial (hr0 : ∀ v, 0 < rho v)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*rho v < dist p (d.point v))
    {e : E} {p : E × Bool} (he : e ≠ p.1) : Disjoint (T.middle e) (T.radial p) := by
  apply Set.disjoint_left.mpr
  intro x hx hp
  exact he (T.middle_radial_intersection hr0 hr hx hp).1

/-- The middle arcs avoid all original vertex positions. -/
theorem point_notMem_middle (e : E) (v : V) : d.point v ∉ T.middle e := by
  rintro ⟨t,ht,h⟩
  exact d.interior_avoids e t (T.middle_inside e ht) v h

end PlaneDrawing.VariableTrimming
end PlanarHom.MultiGraph
