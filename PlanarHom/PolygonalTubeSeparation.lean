import PlanarHom.PolygonalNormals
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Small-width separation of actual polygonal strips

Disjoint compact center segments have disjoint sufficiently thin strips. At a
shared vertex, distinct rays admit a separating linear functional, so the
pinched strips meet only at that vertex for sufficiently small widths.
-/

noncomputable section
open Set unitInterval Filter
open scoped Topology Convex
namespace PlanarHom.Polygonal
open MultiGraph

/-- Uniform tube containment makes separated compact center segments yield
actually disjoint strip images for all sufficiently small widths. -/
theorem eventually_disjoint_strips (P Q R S A B C D : Plane)
    (hsep : Disjoint [P -[ℝ] Q] [R -[ℝ] S]) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      Disjoint (Set.range (stripMap P Q (ε • A) (ε • B)))
        (Set.range (stripMap R S (ε • C) (ε • D))) := by
  have hcomp (x y : Plane) : IsCompact [x -[ℝ] y] := by
    rw [← Path.range_segment]
    exact isCompact_range (Path.segment x y).continuous
  obtain ⟨δ, hδ, hdis⟩ := hsep.exists_thickenings (hcomp P Q) (hcomp R S).isClosed
  have hlim (a b : Plane) : Tendsto (fun ε : ℝ => |ε| * (‖a‖ + ‖b - a‖)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => |ε| * (‖a‖ + ‖b - a‖)) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := (0 : ℝ))
  filter_upwards [(hlim A B).eventually_lt_const hδ, (hlim C D).eventually_lt_const hδ] with ε hε hε'
  have htube (p q a b : Plane) (hb : |ε| * (‖a‖ + ‖b - a‖) < δ) :
      Set.range (stripMap p q (ε • a) (ε • b)) ⊆ Metric.thickening δ [p -[ℝ] q] := by
    rintro z ⟨t, rfl⟩
    apply Metric.mem_thickening_iff.mpr
    refine ⟨Path.segment p q t.1, ?_, (dist_stripMap_segment_le p q a b ε t).trans_lt hb⟩
    rw [← Path.range_segment]
    exact ⟨t.1, rfl⟩
  exact hdis.mono (htube P Q A B hε) (htube R S C D hε')

/-- Distinct incident straight rays admit a signed transverse separator. -/
theorem exists_ray_separator (O P Q : Plane) (hP : O ≠ P) (hQ : O ≠ Q)
    (hinter : ∀ z, z ∈ [O -[ℝ] P] → z ∈ [O -[ℝ] Q] → z = O) :
    ∃ N : Plane, cross (P - O) N < 0 ∧ 0 < cross (Q - O) N := by
  obtain ⟨N, hN, hN'⟩ := exists_transverse_at_corner P O Q hP.symm hQ
    (fun z hz hz' => hinter z (by simpa only [segment_symm] using hz) hz')
  refine ⟨N, ?_, hN'⟩
  have he : O - P = -(P - O) := by abel
  rw [he, cross_neg_left] at hN
  linarith

/-- An exact separating-functional formula for a strip pinched at its first endpoint. -/
theorem cross_pinched_start (O P A N : Plane) (t s : ℝ) :
    cross (strip O P 0 A t s - O) N = t * cross (P - O + s • A) N := by
  simp only [strip, cross_add_left, cross_sub_left, cross_smul_left, cross_zero_left]
  ring

/-- Opposite signed sides force two pinched strips to meet only at their common
endpoint, with both longitudinal parameters zero. -/
theorem pinched_strips_intersection (O P Q A B N : Plane)
    (hP0 : cross (P - O) N < 0) (hP1 : cross (P - O + A) N < 0)
    (hQ0 : 0 < cross (Q - O) N) (hQ1 : 0 < cross (Q - O + B) N)
    (p q : I × I) (heq : stripMap O P 0 A p = stripMap O Q 0 B q) :
    p.1 = 0 ∧ q.1 = 0 := by
  have hneg : cross (P - O + (p.2 : ℝ) • A) N < 0 := by
    rw [cross_interpolate]
    have h := closed_combo_pos (neg_pos.mpr hP0) (neg_pos.mpr hP1) p.2.2.1 p.2.2.2
    nlinarith
  have hpos : 0 < cross (Q - O + (q.2 : ℝ) • B) N := by
    rw [cross_interpolate]
    exact closed_combo_pos hQ0 hQ1 q.2.2.1 q.2.2.2
  have hc := congrArg (fun Z : Plane => cross (Z - O) N) heq
  change cross (strip O P 0 A p.1 p.2 - O) N =
    cross (strip O Q 0 B q.1 q.2 - O) N at hc
  rw [cross_pinched_start, cross_pinched_start] at hc
  have hp0 : (p.1 : ℝ) * cross (P - O + (p.2 : ℝ) • A) N = 0 := by
    have hleft := mul_nonpos_of_nonneg_of_nonpos p.1.2.1 hneg.le
    have hright := mul_nonneg q.1.2.1 hpos.le
    linarith
  have hq0 : (q.1 : ℝ) * cross (Q - O + (q.2 : ℝ) • B) N = 0 := by linarith
  exact ⟨Subtype.ext ((mul_eq_zero.mp hp0).resolve_right (ne_of_lt hneg)),
    Subtype.ext ((mul_eq_zero.mp hq0).resolve_right (ne_of_gt hpos))⟩

/-- Distinct original rays remain disjoint away from their shared vertex for
all sufficiently small perturbation widths. -/
theorem eventually_pinched_strips_intersect_only_at_vertex (O P Q A B : Plane)
    (hP : O ≠ P) (hQ : O ≠ Q)
    (hinter : ∀ z, z ∈ [O -[ℝ] P] → z ∈ [O -[ℝ] Q] → z = O) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ p q : I × I,
      stripMap O P 0 (ε • A) p = stripMap O Q 0 (ε • B) q → p.1 = 0 ∧ q.1 = 0 := by
  obtain ⟨N, hN, hN'⟩ := exists_ray_separator O P Q hP hQ hinter
  have hlim (P A : Plane) :
      Tendsto (fun ε : ℝ => cross (P - O + ε • A) N) (𝓝 0) (𝓝 (cross (P - O) N)) := by
    have hc : Continuous (fun ε : ℝ => cross (P - O + ε • A) N) := by unfold cross; fun_prop
    simpa using hc.continuousAt.tendsto (x := (0 : ℝ))
  filter_upwards [(hlim P A).eventually_lt_const hN, (hlim Q B).eventually_const_lt hN']
    with ε hεP hεQ
  intro p q heq
  exact pinched_strips_intersection O P Q (ε • A) (ε • B) N hN hεP hN' hεQ p q heq

/-- Reversing an explicit strip merely reverses its longitudinal coordinate. -/
theorem strip_reverse (P Q A B : Plane) (t s : ℝ) :
    strip P Q A B t s = strip Q P B A (1 - t) s := by
  unfold strip
  module


/-- A positive transverse direction remains positive after a small linear
longitudinal perturbation and a positive scaling. -/
theorem eventually_scaled_transverse_positive (D M N : Plane) (h : 0 < cross D N) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, 0 < cross (D + ε • M) (ε • N) := by
  have hlim : Tendsto (fun ε : ℝ => cross (D + ε • M) N) (𝓝 0) (𝓝 (cross D N)) := by
    have hc : Continuous (fun ε : ℝ => cross (D + ε • M) N) := by unfold cross; fun_prop
    simpa using hc.continuousAt.tendsto (x := (0 : ℝ))
  have he := (hlim.eventually_const_lt h).filter_mono
    (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0 from nhdsWithin_le_nhds)
  filter_upwards [he, self_mem_nhdsWithin] with ε hε hpos
  simpa only [cross_smul_right] using mul_pos (show 0 < ε from hpos) hε

/-- Every sufficiently small positive width separates two adjacent polygonal
pieces by their shared transverse cross-section. -/
theorem eventually_adjacent_strip_intersection (P Q R A N B : Plane)
    (hP : 0 < cross (Q - P) N) (hQ : 0 < cross (R - Q) N) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ∀ p q : I × I,
      stripMap P Q (ε • A) (ε • N) p = stripMap Q R (ε • N) (ε • B) q →
        p.1 = 1 ∧ q.1 = 0 ∧ p.2 = q.2 := by
  filter_upwards [eventually_scaled_transverse_positive (Q - P) (N - A) N hP,
    eventually_scaled_transverse_positive (R - Q) (B - N) N hQ,
    self_mem_nhdsWithin] with ε hεP hεQ hε
  intro p q heq
  apply adjacent_strip_intersection P Q R (ε • A) (ε • N) (ε • B)
    (by simpa using mul_pos (show 0 < ε from hε) hP)
    (by simpa only [← smul_sub] using hεP)
    (by simpa using mul_pos (show 0 < ε from hε) hQ)
    (by simpa only [← smul_sub] using hεQ) p q heq

/-- The positive transverse determinant prevents a pinched strip from returning
to its pinched initial vertex at any positive longitudinal parameter. -/
theorem pinched_strip_ne_start (O P B : Plane) (h : 0 < cross (P - O) B)
    (p : I × I) (hp : 0 < (p.1 : ℝ)) : stripMap O P 0 B p ≠ O := by
  intro heq
  have hc := congrArg (fun Z : Plane => cross (Z - O) B) heq
  change cross (strip O P 0 B p.1 p.2 - O) B = cross (O - O) B at hc
  rw [cross_pinched_start] at hc
  simp only [cross_add_left, cross_smul_left, cross_self, mul_zero, add_zero,
    sub_self, cross_zero_left] at hc
  exact (ne_of_gt (mul_pos hp h)) hc

/-- A disjoint original vertex remains outside every sufficiently thin strip. -/
theorem eventually_strip_avoids_point (P Q A B X : Plane) (hX : X ∉ [P -[ℝ] Q]) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ p : I × I, stripMap P Q (ε • A) (ε • B) p ≠ X := by
  have hsep : Disjoint [P -[ℝ] Q] [X -[ℝ] X] := by
    rw [segment_same]
    exact Set.disjoint_singleton_right.mpr hX
  filter_upwards [eventually_disjoint_strips P Q X X A B 0 0 hsep] with ε hε
  intro p hp
  apply Set.disjoint_left.mp hε ⟨p, hp⟩
  exact ⟨(0, 0), by simp [stripMap]⟩

end PlanarHom.Polygonal
