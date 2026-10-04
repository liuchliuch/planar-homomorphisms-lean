import PlanarHom.PolygonalNormalAssignment

/-!
# Equality of underlying center points from thin-strip intersections

This API composes the numerical strip cases used in global finite band gluing.
It handles orientation reversal explicitly, so the shared host endpoint may
occur at either end of either directed segment.
-/

noncomputable section
open Set unitInterval Filter
open scoped Topology Convex
namespace PlanarHom.Polygonal
open MultiGraph

/-- A strip intersection forces equality of the underlying unperturbed points. -/
def StripCentersAgree (P Q A B R S C D : Plane) : Prop :=
  ∀ p q : I × I, stripMap P Q A B p = stripMap R S C D q →
    AffineMap.lineMap P Q (p.1 : ℝ) = AffineMap.lineMap R S (q.1 : ℝ)

namespace StripCentersAgree
variable {P Q A B R S C D : Plane}

theorem symm (h : StripCentersAgree P Q A B R S C D) : StripCentersAgree R S C D P Q A B :=
  fun p q hpq => (h q p hpq.symm).symm

/-- Orientation reversal has no effect on the center-equality condition. -/
theorem reverse_left (h : StripCentersAgree Q P B A R S C D) :
    StripCentersAgree P Q A B R S C D := by
  intro p q hpq
  let p' : I × I := (unitInterval.symm p.1, p.2)
  have hm : stripMap Q P B A p' = stripMap P Q A B p := by
    change strip Q P B A (1 - (p.1 : ℝ)) p.2 = strip P Q A B p.1 p.2
    exact (strip_reverse P Q A B p.1 p.2).symm
  have he := h p' q (hm.trans hpq)
  change AffineMap.lineMap Q P (1 - (p.1 : ℝ)) = AffineMap.lineMap R S (q.1 : ℝ) at he
  rwa [AffineMap.lineMap_apply_one_sub] at he

theorem reverse_right (h : StripCentersAgree P Q A B S R D C) :
    StripCentersAgree P Q A B R S C D := h.symm.reverse_left.symm

theorem of_disjoint (h : Disjoint (Set.range (stripMap P Q A B)) (Set.range (stripMap R S C D))) :
    StripCentersAgree P Q A B R S C D := by
  intro p q hpq
  exact (Set.disjoint_left.mp h ⟨p, rfl⟩ ⟨q, hpq.symm⟩).elim

end StripCentersAgree

/-- The disjoint-center-segment case. -/
theorem eventually_centersAgree_of_disjoint (P Q R S A B C D : Plane)
    (hsep : Disjoint [P -[ℝ] Q] [R -[ℝ] S]) :
    ∀ᶠ ε : ℝ in 𝓝 0, StripCentersAgree P Q (ε • A) (ε • B) R S (ε • C) (ε • D) :=
  (eventually_disjoint_strips P Q R S A B C D hsep).mono fun _ h => .of_disjoint h

/-- The self-piece case, including genuinely collapsed endpoint sides. -/
theorem eventually_centersAgree_self (P Q A B : Plane)
    (hA : A = 0 ∨ 0 < cross (Q - P) A)
    (hB : B = 0 ∨ 0 < cross (Q - P) B) (hne : A ≠ 0 ∨ B ≠ 0) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0,
      StripCentersAgree P Q (ε • A) (ε • B) P Q (ε • A) (ε • B) := by
  filter_upwards [eventually_strip_eq_or_pinched_endpoint P Q A B hA hB hne] with ε hε
  intro p q hpq
  rcases hε p q hpq with rfl | ⟨_, hp, hq⟩ | ⟨_, hp, hq⟩
  · rfl
  · simp [hp, hq]
  · simp [hp, hq]

/-- Two actual consecutive pieces give the same center point whenever their
sufficiently thin strips meet. -/
theorem eventually_centersAgree_adjacent (P Q R A N B : Plane)
    (hP : 0 < cross (Q - P) N) (hQ : 0 < cross (R - Q) N) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0,
      StripCentersAgree P Q (ε • A) (ε • N) Q R (ε • N) (ε • B) := by
  filter_upwards [eventually_adjacent_strip_intersection P Q R A N B hP hQ] with ε hε
  intro p q hpq
  obtain ⟨hp, hq, _⟩ := hε p q hpq
  simp [hp, hq]

/-- Two outward-oriented pinched rays meet only over their common center vertex. -/
theorem eventually_centersAgree_rays (O P Q A B : Plane) (hP : O ≠ P) (hQ : O ≠ Q)
    (hinter : ∀ z, z ∈ [O -[ℝ] P] → z ∈ [O -[ℝ] Q] → z = O) :
    ∀ᶠ ε : ℝ in 𝓝 0, StripCentersAgree O P 0 (ε • A) O Q 0 (ε • B) := by
  filter_upwards [eventually_pinched_strips_intersect_only_at_vertex O P Q A B hP hQ hinter]
    with ε hε
  intro p q hpq
  obtain ⟨hp, hq⟩ := hε p q hpq
  simp [hp, hq]

/-- All four possible orientations at a shared host vertex are covered. -/
theorem eventually_centersAgree_at_host (P Q R S X : Plane) (N : Plane → Plane)
    (hPQ : P ≠ Q) (hRS : R ≠ S) (hX : N X = 0)
    (hleft : P = X ∨ Q = X) (hright : R = X ∨ S = X)
    (hinter : ∀ z, z ∈ [P -[ℝ] Q] → z ∈ [R -[ℝ] S] → z = X) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      StripCentersAgree P Q (ε • N P) (ε • N Q) R S (ε • N R) (ε • N S) := by
  rcases hleft with rfl | rfl
  · rcases hright with rfl | rfl
    · simpa only [hX, smul_zero] using
        eventually_centersAgree_rays R Q S (N Q) (N S) hPQ hRS hinter
    · have hi : ∀ z, z ∈ [S -[ℝ] Q] → z ∈ [S -[ℝ] R] → z = S := by
        intro z hz hz'
        exact hinter z hz (by simpa only [segment_symm] using hz')
      filter_upwards [eventually_centersAgree_rays S Q R (N Q) (N R) hPQ hRS.symm hi] with ε hε
      simpa only [hX, smul_zero] using hε.reverse_right
  · rcases hright with rfl | rfl
    · have hi : ∀ z, z ∈ [R -[ℝ] P] → z ∈ [R -[ℝ] S] → z = R := by
        intro z hz hz'
        exact hinter z (by simpa only [segment_symm] using hz) hz'
      filter_upwards [eventually_centersAgree_rays R P S (N P) (N S) hPQ.symm hRS hi] with ε hε
      simpa only [hX, smul_zero] using hε.reverse_left
    · have hi : ∀ z, z ∈ [S -[ℝ] P] → z ∈ [S -[ℝ] R] → z = S := by
        intro z hz hz'
        exact hinter z (by simpa only [segment_symm] using hz)
          (by simpa only [segment_symm] using hz')
      filter_upwards [eventually_centersAgree_rays S P R (N P) (N R) hPQ.symm hRS.symm hi] with ε hε
      simpa only [hX, smul_zero] using hε.reverse_left.reverse_right


/-- Actual finite segment incidence: two distinct pieces are disjoint or meet
only at one common endpoint. This states geometric intersections, not strip
compatibility or planarity preservation. -/
def EndpointIntersections (S : Set (Plane × Plane)) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
    Disjoint [e.1 -[ℝ] e.2] [f.1 -[ℝ] f.2] ∨
    ∃ X : Plane, (e.1 = X ∨ e.2 = X) ∧ (f.1 = X ∨ f.2 = X) ∧
      ∀ z, z ∈ [e.1 -[ℝ] e.2] → z ∈ [f.1 -[ℝ] f.2] → z = X

/-- A single sufficiently small width satisfies center compatibility for every
pair of pieces of a finite polygonal drawing. -/
theorem eventually_all_strip_centers_agree (S : Finset (Plane × Plane)) (H : Set Plane)
    (N : Plane → Plane) (hcorner : TwoValentCorners (S : Set (Plane × Plane)) H)
    (hpair : EndpointIntersections (S : Set (Plane × Plane)))
    (hne : ∀ e ∈ S, e.1 ≠ e.2)
    (hzero : ∀ x ∈ H, N x = 0)
    (hout : ∀ a b, (a, b) ∈ S → a ∉ H → 0 < cross (b - a) (N a))
    (hin : ∀ a b, (a, b) ∈ S → b ∉ H → 0 < cross (b - a) (N b))
    (hfree : ∀ a b, (a, b) ∈ S → a ∉ H ∨ b ∉ H) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ∀ e ∈ S, ∀ f ∈ S,
      StripCentersAgree e.1 e.2 (ε • N e.1) (ε • N e.2)
        f.1 f.2 (ε • N f.1) (ε • N f.2) := by
  apply (Filter.eventually_all_finset S).mpr
  intro e he
  apply (Filter.eventually_all_finset S).mpr
  intro f hf
  by_cases hef : e = f
  · subst f
    have hA : N e.1 = 0 ∨ 0 < cross (e.2 - e.1) (N e.1) := by
      by_cases h : e.1 ∈ H
      · exact Or.inl (hzero _ h)
      · exact Or.inr (hout _ _ he h)
    have hB : N e.2 = 0 ∨ 0 < cross (e.2 - e.1) (N e.2) := by
      by_cases h : e.2 ∈ H
      · exact Or.inl (hzero _ h)
      · exact Or.inr (hin _ _ he h)
    have hn : N e.1 ≠ 0 ∨ N e.2 ≠ 0 := by
      rcases hfree _ _ he with h | h
      · exact Or.inl (fun hz => by simpa [hz] using hout _ _ he h)
      · exact Or.inr (fun hz => by simpa [hz] using hin _ _ he h)
    exact eventually_centersAgree_self e.1 e.2 (N e.1) (N e.2) hA hB hn
  · rcases hpair e he f hf hef with hdis | ⟨X, hleft, hright, hinter⟩
    · exact (eventually_centersAgree_of_disjoint e.1 e.2 f.1 f.2
        (N e.1) (N e.2) (N f.1) (N f.2) hdis).filter_mono nhdsWithin_le_nhds
    · by_cases hX : X ∈ H
      · exact (eventually_centersAgree_at_host e.1 e.2 f.1 f.2 X N
          (hne e he) (hne f hf) (hzero X hX) hleft hright hinter).filter_mono nhdsWithin_le_nhds
      · obtain ⟨P, Q, _, _, _, hsucc, hpred⟩ := hcorner X hX ⟨e.1, e.2, he, hleft⟩
        rcases hleft with heX | heX <;> rcases hright with hfX | hfX
        · exact (hef (Prod.ext (heX.trans hfX.symm)
            ((hsucc _ _ he heX).trans (hsucc _ _ hf hfX).symm))).elim
        · have hcrossF : 0 < cross (X - f.1) (N X) := by
            simpa only [hfX] using hin _ _ hf (by simpa only [hfX] using hX)
          have hcrossE : 0 < cross (e.2 - X) (N X) := by
            simpa only [heX] using hout _ _ he (by simpa only [heX] using hX)
          filter_upwards [eventually_centersAgree_adjacent f.1 X e.2
            (N f.1) (N X) (N e.2) hcrossF hcrossE] with ε hε
          simpa only [heX, hfX] using hε.symm
        · have hcrossE : 0 < cross (X - e.1) (N X) := by
            simpa only [heX] using hin _ _ he (by simpa only [heX] using hX)
          have hcrossF : 0 < cross (f.2 - X) (N X) := by
            simpa only [hfX] using hout _ _ hf (by simpa only [hfX] using hX)
          filter_upwards [eventually_centersAgree_adjacent e.1 X f.2
            (N e.1) (N X) (N f.2) hcrossE hcrossF] with ε hε
          simpa only [heX, hfX] using hε
        · exact (hef (Prod.ext ((hpred _ _ he heX).trans (hpred _ _ hf hfX).symm)
            (heX.trans hfX.symm))).elim

end PlanarHom.Polygonal
