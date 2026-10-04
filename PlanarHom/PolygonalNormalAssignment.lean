import PlanarHom.PolygonalClosedStrips

/-!
# A simultaneous normal assignment for a finite polygonal graph

Every non-host subdivision point has its actual unique incoming and outgoing
segments, meeting only at that point. The proved planar corner lemma chooses
one positive normal for both segments; host vertices get normal zero. No normal
or ribbon-existence conclusion is included in the incidence premise.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Set unitInterval Filter
open scoped Topology Convex
namespace PlanarHom.Polygonal
open MultiGraph

/-- A point occurs as an endpoint of one of the specified straight pieces. -/
def Touches (S : Set (Plane × Plane)) (x : Plane) : Prop :=
  ∃ a b, (a, b) ∈ S ∧ (a = x ∨ b = x)

/-- Exact directed valence two at each non-host polygonal subdivision point,
with the two actual incident segments meeting only at that corner. -/
def TwoValentCorners (S : Set (Plane × Plane)) (H : Set Plane) : Prop :=
  ∀ x, x ∉ H → Touches S x → ∃ P Q,
    P ≠ x ∧ x ≠ Q ∧
    (∀ z, z ∈ [P -[ℝ] x] → z ∈ [x -[ℝ] Q] → z = x) ∧
    (∀ a b, (a, b) ∈ S → a = x → b = Q) ∧
    (∀ a b, (a, b) ∈ S → b = x → a = P)

/-- One global assignment serves every incident piece simultaneously. It is
zero on host vertices and positive transverse at all other segment endpoints. -/
theorem exists_normal_assignment (S : Set (Plane × Plane)) (H : Set Plane)
    (hcorner : TwoValentCorners S H) :
    ∃ N : Plane → Plane, (∀ x ∈ H, N x = 0) ∧
      (∀ a b, (a, b) ∈ S → a ∉ H → 0 < cross (b - a) (N a)) ∧
      (∀ a b, (a, b) ∈ S → b ∉ H → 0 < cross (b - a) (N b)) := by
  have hpoint (x : Plane) : ∃ N : Plane,
      (x ∈ H → N = 0) ∧
      (∀ a b, (a, b) ∈ S → a = x → x ∉ H → 0 < cross (b - a) N) ∧
      (∀ a b, (a, b) ∈ S → b = x → x ∉ H → 0 < cross (b - a) N) := by
    by_cases hx : x ∈ H
    · exact ⟨0, fun _ => rfl, fun _ _ _ _ hn => (hn hx).elim,
        fun _ _ _ _ hn => (hn hx).elim⟩
    · by_cases htouch : Touches S x
      · obtain ⟨P, Q, hPx, hxQ, hinter, hout, hin⟩ := hcorner x hx htouch
        obtain ⟨N, hNin, hNout⟩ := exists_transverse_at_corner P x Q hPx hxQ hinter
        refine ⟨N, fun h => (hx h).elim, ?_, ?_⟩
        · intro a b hab ha _
          have hb := hout a b hab ha
          simpa only [ha, hb] using hNout
        · intro a b hab hb _
          have ha := hin a b hab hb
          simpa only [ha, hb] using hNin
      · refine ⟨0, fun h => (hx h).elim, ?_, ?_⟩
        · intro a b hab ha _
          exact (htouch ⟨a, b, hab, Or.inl ha⟩).elim
        · intro a b hab hb _
          exact (htouch ⟨a, b, hab, Or.inr hb⟩).elim
  choose N hzero hout hin using hpoint
  exact ⟨N, hzero, fun a b hab ha => hout a a b hab rfl ha,
    fun a b hab hb => hin b a b hab rfl hb⟩

/-- The selected normal is nonzero at every non-host incident endpoint. -/
theorem normal_ne_zero_at_nonhost {S : Set (Plane × Plane)} {H : Set Plane}
    (N : Plane → Plane)
    (hout : ∀ a b, (a, b) ∈ S → a ∉ H → 0 < cross (b - a) (N a))
    (hin : ∀ a b, (a, b) ∈ S → b ∉ H → 0 < cross (b - a) (N b))
    (x : Plane) (hx : x ∉ H) (htouch : Touches S x) : N x ≠ 0 := by
  obtain ⟨a, b, hab, ha | hb⟩ := htouch
  · subst a
    intro hz
    have h := hout x b hab hx
    simpa [hz] using h
  · subst b
    intro hz
    have h := hin a x hab hx
    simpa [hz] using h

/-- For finitely many straight pieces, one sufficiently small width works for
all self-equality classifications simultaneously. -/
theorem eventually_all_strip_self_equalities (S : Finset (Plane × Plane)) (H : Set Plane)
    (N : Plane → Plane) (hzero : ∀ x ∈ H, N x = 0)
    (hout : ∀ a b, (a, b) ∈ S → a ∉ H → 0 < cross (b - a) (N a))
    (hin : ∀ a b, (a, b) ∈ S → b ∉ H → 0 < cross (b - a) (N b))
    (hfree : ∀ a b, (a, b) ∈ S → a ∉ H ∨ b ∉ H) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ∀ e ∈ S, ∀ p q : I × I,
      stripMap e.1 e.2 (ε • N e.1) (ε • N e.2) p =
        stripMap e.1 e.2 (ε • N e.1) (ε • N e.2) q →
      p = q ∨ (e.1 ∈ H ∧ p.1 = 0 ∧ q.1 = 0) ∨ (e.2 ∈ H ∧ p.1 = 1 ∧ q.1 = 1) := by
  apply (Filter.eventually_all_finset S).mpr
  intro e he
  have hA : N e.1 = 0 ∨ 0 < cross (e.2 - e.1) (N e.1) := by
    by_cases h : e.1 ∈ H
    · exact Or.inl (hzero e.1 h)
    · exact Or.inr (hout e.1 e.2 he h)
  have hB : N e.2 = 0 ∨ 0 < cross (e.2 - e.1) (N e.2) := by
    by_cases h : e.2 ∈ H
    · exact Or.inl (hzero e.2 h)
    · exact Or.inr (hin e.1 e.2 he h)
  have hne : N e.1 ≠ 0 ∨ N e.2 ≠ 0 := by
    rcases hfree e.1 e.2 he with h | h
    · exact Or.inl (fun hz => by simpa [hz] using hout e.1 e.2 he h)
    · exact Or.inr (fun hz => by simpa [hz] using hin e.1 e.2 he h)
  filter_upwards [eventually_strip_eq_or_pinched_endpoint e.1 e.2 (N e.1) (N e.2) hA hB hne]
    with ε hε
  intro p q hpq
  rcases hε p q hpq with h | ⟨hz, hp, hq⟩ | ⟨hz, hp, hq⟩
  · exact Or.inl h
  · have hh : e.1 ∈ H := by
      by_contra hn
      simpa [hz] using hout e.1 e.2 he hn
    exact Or.inr (Or.inl ⟨hh, hp, hq⟩)
  · have hh : e.2 ∈ H := by
      by_contra hn
      simpa [hz] using hin e.1 e.2 he hn
    exact Or.inr (Or.inr ⟨hh, hp, hq⟩)

end PlanarHom.Polygonal
