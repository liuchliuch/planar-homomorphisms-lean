import PlanarHom.PlanarNeighborhoods
import Mathlib.Topology.Order.IntermediateValue

/-!
# Last/first sphere crossings and disjoint middle arcs

The truncation is constructed from arbitrary continuous edge curves using the
intermediate value theorem and maxima/minima of compact level sets. All resulting
middle arcs stay outside the open vertex balls; their interiors stay strictly
outside the closed balls. In particular loops retain two distinct ports.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph
namespace PlaneDrawing

/-- Last crossing of a level between strictly separated endpoint values. -/
theorem last_level_crossing (f : C(I, ℝ)) {a b : I} (hab : a ≤ b) {r : ℝ}
    (ha : f a < r) (hb : r < f b) :
    ∃ s ∈ Set.Ioo a b, f s = r ∧ ∀ t ∈ Set.Ioc s b, r < f t := by
  let S : Set I := Set.Icc a b ∩ f ⁻¹' {r}
  have hc : IsCompact S := isCompact_Icc.inter_right
    ((isClosed_singleton : IsClosed ({r} : Set ℝ)).preimage f.continuous)
  have hn : S.Nonempty := by
    obtain ⟨s,hs,hfs⟩ := intermediate_value_Icc hab f.continuous.continuousOn ⟨ha.le,hb.le⟩
    exact ⟨s,hs,hfs⟩
  obtain ⟨s,hs,hmax⟩ := hc.exists_isGreatest hn
  have hfs : f s = r := hs.2
  have has : a < s := lt_of_le_of_ne hs.1.1 (by intro h; subst s; linarith)
  have hsb : s < b := lt_of_le_of_ne hs.1.2 (by intro h; subst s; linarith)
  refine ⟨s,⟨has,hsb⟩,hfs,?_⟩
  intro t ht
  by_contra h
  obtain ⟨u,hu,hfu⟩ := intermediate_value_Icc ht.2 f.continuous.continuousOn
    ⟨le_of_not_gt h,hb.le⟩
  have hus : u ≤ s := hmax ⟨⟨has.le.trans (ht.1.le.trans hu.1),hu.2⟩,hfu⟩
  exact (ht.1.trans_le hu.1).not_ge hus

/-- First crossing of a level when the function starts strictly above it. -/
theorem first_level_crossing (f : C(I, ℝ)) {a b : I} (hab : a ≤ b) {r : ℝ}
    (ha : r < f a) (hb : f b < r) :
    ∃ s ∈ Set.Ioo a b, f s = r ∧ ∀ t ∈ Set.Ico a s, r < f t := by
  let S : Set I := Set.Icc a b ∩ f ⁻¹' {r}
  have hc : IsCompact S := isCompact_Icc.inter_right
    ((isClosed_singleton : IsClosed ({r} : Set ℝ)).preimage f.continuous)
  have hn : S.Nonempty := by
    obtain ⟨s,hs,hfs⟩ := intermediate_value_Icc' hab f.continuous.continuousOn ⟨hb.le,ha.le⟩
    exact ⟨s,hs,hfs⟩
  obtain ⟨s,hs,hmin⟩ := hc.exists_isLeast hn
  have hfs : f s = r := hs.2
  have has : a < s := lt_of_le_of_ne hs.1.1 (by intro h; subst s; linarith)
  have hsb : s < b := lt_of_le_of_ne hs.1.2 (by intro h; subst s; linarith)
  refine ⟨s,⟨has,hsb⟩,hfs,?_⟩
  intro t ht
  by_contra h
  obtain ⟨u,hu,hfu⟩ := intermediate_value_Icc' ht.1 f.continuous.continuousOn
    ⟨le_of_not_gt h,ha.le⟩
  have hsu : s ≤ u := hmin ⟨⟨hu.1,hu.2.trans (ht.2.le.trans hsb.le)⟩,hfu⟩
  exact (hu.2.trans_lt ht.2).not_ge hsu

variable {V E : Type*} {G : MultiGraph V E}

/-- The two ports for each edge and verified one-sided distance inequalities. -/
structure Trimming (d : PlaneDrawing G) (r : ℝ) where
  left : E → I
  right : E → I
  left_bounds : ∀ e, left e ∈ Set.Ioo 0 firstThird
  right_bounds : ∀ e, right e ∈ Set.Ioo secondThird 1
  left_sphere : ∀ e, dist (d.curve e (left e)) (d.point (G.src e)) = r
  right_sphere : ∀ e, dist (d.curve e (right e)) (d.point (G.dst e)) = r
  source_tail : ∀ e t, t ∈ Set.Ioc (left e) firstThird →
    r < dist (d.curve e t) (d.point (G.src e))
  destination_tail : ∀ e t, t ∈ Set.Ico secondThird (right e) →
    r < dist (d.curve e t) (d.point (G.dst e))

/-- Construct the ports from the ordinary drawing and its proved uniform radius. -/
def trimming (d : PlaneDrawing G) {r : ℝ} (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v)) : Trimming d r := by
  have hleft : ∀ e, ∃ s ∈ Set.Ioo (0 : I) firstThird,
      dist (d.curve e s) (d.point (G.src e)) = r ∧
      ∀ t ∈ Set.Ioc s firstThird, r < dist (d.curve e t) (d.point (G.src e)) := by
    intro e
    let f : C(I,ℝ) := ⟨fun t => dist (d.curve e t) (d.point (G.src e)), by fun_prop⟩
    apply last_level_crossing f (show (0 : I) ≤ firstThird from bot_le)
    · simpa [f,d.curve_zero] using hr0
    · have h := d.radius_middle_separation hr e firstThird
        ⟨le_rfl,firstThird_lt_secondThird.le⟩ (G.src e)
      dsimp [f]
      linarith
  have hright : ∀ e, ∃ s ∈ Set.Ioo secondThird (1 : I),
      dist (d.curve e s) (d.point (G.dst e)) = r ∧
      ∀ t ∈ Set.Ico secondThird s, r < dist (d.curve e t) (d.point (G.dst e)) := by
    intro e
    let f : C(I,ℝ) := ⟨fun t => dist (d.curve e t) (d.point (G.dst e)), by fun_prop⟩
    apply first_level_crossing f (show secondThird ≤ (1 : I) from le_top)
    · have h := d.radius_middle_separation hr e secondThird
        ⟨firstThird_lt_secondThird.le,le_rfl⟩ (G.dst e)
      dsimp [f]
      linarith
    · simpa [f,d.curve_one] using hr0
  choose left hl hs htail using hleft
  choose right hr' ht htail' using hright
  exact ⟨left,right,hl,hr',hs,ht,htail,htail'⟩

namespace Trimming
variable {d : PlaneDrawing G} {r : ℝ} (T : Trimming d r)

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
theorem middle_strictly_outside (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    (e : E) (t : I) (ht : t ∈ Set.Ioo (T.left e) (T.right e)) (v : V) :
    r < dist (d.curve e t) (d.point v) := by
  by_cases ha : t ≤ firstThird
  · by_cases hv : G.src e = v
    · simpa [hv] using T.source_tail e t ⟨ht.1,ha⟩
    · have h := hr v (d.curve e t) (Or.inr (Set.mem_iUnion.mpr
        ⟨e,t,⟨by simp [portLo,hv], ha.trans
          (firstThird_lt_secondThird.le.trans (secondThird_le_portHi v e))⟩,rfl⟩))
      linarith
  · by_cases hb : t ≤ secondThird
    · have h := d.radius_middle_separation hr e t ⟨(lt_of_not_ge ha).le,hb⟩ v
      linarith
    · by_cases hv : G.dst e = v
      · simpa [hv] using T.destination_tail e t ⟨(lt_of_not_ge hb).le,ht.2⟩
      · have h := hr v (d.curve e t) (Or.inr (Set.mem_iUnion.mpr
          ⟨e,t,⟨(portLo_le_firstThird v e).trans (lt_of_not_ge ha).le,
            by simp only [portHi,if_neg hv]; exact le_top⟩,rfl⟩))
        linarith

/-- Closed trimmed arcs stay outside open vertex balls, with possible equality
only at their own source/destination ports. -/
theorem middle_outside (hr0 : 0 < r)
    (hr : ∀ v p, p ∈ d.forbidden v → 4*r < dist p (d.point v))
    (e : E) (t : I) (ht : t ∈ Set.Icc (T.left e) (T.right e)) (v : V) :
    r ≤ dist (d.curve e t) (d.point v) := by
  by_cases hl : t = T.left e
  · subst t
    by_cases hv : G.src e = v
    · simpa [hv] using (T.left_sphere e).ge
    · have h := hr v (d.curve e (T.left e)) (Or.inr (Set.mem_iUnion.mpr
        ⟨e,T.left e,⟨by simp [portLo,hv], (T.left_bounds e).2.le.trans
          (firstThird_lt_secondThird.le.trans (secondThird_le_portHi v e))⟩,rfl⟩))
      linarith
  · by_cases hr' : t = T.right e
    · subst t
      by_cases hv : G.dst e = v
      · simpa [hv] using (T.right_sphere e).ge
      · have h := hr v (d.curve e (T.right e)) (Or.inr (Set.mem_iUnion.mpr
          ⟨e,T.right e,⟨(portLo_le_firstThird v e).trans
            (firstThird_lt_secondThird.le.trans (T.right_bounds e).1.le),
            by simp only [portHi,if_neg hv]; exact le_top⟩,rfl⟩))
        linarith
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

end Trimming
end PlaneDrawing
end PlanarHom.MultiGraph
