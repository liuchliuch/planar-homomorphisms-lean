import PlanarHom.PolygonalStripCompatibility

/-!
# An actual common positive width for all finite polygonal strips

Finite incidence and corner geometry yield one global normal assignment and a
single positive width, as small as requested, for which every strip equality
and host-point equality has the required geometric classification.
-/

noncomputable section
open Set unitInterval Filter
open scoped Topology Convex
namespace PlanarHom.Polygonal
open MultiGraph

/-- Original host vertices occur only at endpoints of straight pieces. -/
def HostEndpointOnly (S : Set (Plane × Plane)) (H : Set Plane) : Prop :=
  ∀ e ∈ S, ∀ X ∈ H, X ∈ [e.1 -[ℝ] e.2] → X = e.1 ∨ X = e.2

/-- Host-point equality for every sufficiently thin strip recovers equality of
the unperturbed center point. -/
theorem eventually_all_strips_respect_hosts (S : Finset (Plane × Plane)) (H : Set Plane)
    (hH : H.Finite) (N : Plane → Plane) (hvertex : HostEndpointOnly (S : Set (Plane × Plane)) H)
    (hzero : ∀ x ∈ H, N x = 0)
    (hout : ∀ a b, (a, b) ∈ S → a ∉ H → 0 < cross (b - a) (N a))
    (hin : ∀ a b, (a, b) ∈ S → b ∉ H → 0 < cross (b - a) (N b))
    (hfree : ∀ a b, (a, b) ∈ S → a ∉ H ∨ b ∉ H) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ∀ e ∈ S, ∀ X ∈ H, ∀ p : I × I,
      stripMap e.1 e.2 (ε • N e.1) (ε • N e.2) p = X →
        AffineMap.lineMap e.1 e.2 (p.1 : ℝ) = X := by
  apply (Filter.eventually_all_finset S).mpr
  intro e he
  apply hH.eventually_all.mpr
  intro X hX
  by_cases hseg : X ∈ [e.1 -[ℝ] e.2]
  · rcases hvertex e he X hX hseg with rfl | rfl
    · have hnon : e.2 ∉ H := (hfree _ _ he).resolve_left (fun h => h hX)
      have hz : N e.1 = 0 := hzero _ hX
      filter_upwards [self_mem_nhdsWithin] with ε hε
      intro p hp
      have hB : 0 < cross (e.2 - e.1) (ε • N e.2) := by
        simpa using mul_pos (show 0 < ε from hε) (hin _ _ he hnon)
      have hp' : stripMap e.1 e.2 0 (ε • N e.2) p = e.1 := by
        simpa only [hz, smul_zero] using hp
      have h0 : stripMap e.1 e.2 0 (ε • N e.2) (0, 0) = e.1 := by simp
      have hparam : p.1 = 0 := by
        rcases pinched_start_eq_or_endpoint e.1 e.2 (ε • N e.2) hB p (0, 0)
          (hp'.trans h0.symm) with h | h
        · exact congrArg Prod.fst h
        · exact h.1
      simp [hparam]
    · have hnon : e.1 ∉ H := (hfree _ _ he).resolve_right (fun h => h hX)
      have hz : N e.2 = 0 := hzero _ hX
      filter_upwards [self_mem_nhdsWithin] with ε hε
      intro p hp
      have hA : 0 < cross (e.2 - e.1) (ε • N e.1) := by
        simpa using mul_pos (show 0 < ε from hε) (hout _ _ he hnon)
      have hp' : stripMap e.1 e.2 (ε • N e.1) 0 p = e.2 := by
        simpa only [hz, smul_zero] using hp
      have h1 : stripMap e.1 e.2 (ε • N e.1) 0 (1, 0) = e.2 := by simp
      have hparam : p.1 = 1 := by
        rcases pinched_end_eq_or_endpoint e.1 e.2 (ε • N e.1) hA p (1, 0)
          (hp'.trans h1.symm) with h | h
        · exact congrArg Prod.fst h
        · exact h.1
      simp [hparam]
  · have havoid := (eventually_strip_avoids_point e.1 e.2 (N e.1) (N e.2) X hseg).filter_mono
      (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0 from nhdsWithin_le_nhds)
    exact havoid.mono fun ε hε p hp => (hε p hp).elim

/-- Three explicit properties of the actual strips at a fixed width: local
parameter equality, global center compatibility, and host-point compatibility. -/
def GoodStripWidth (S : Finset (Plane × Plane)) (H : Set Plane) (N : Plane → Plane) (ε : ℝ) : Prop :=
  (∀ e ∈ S, ∀ p q : I × I,
    stripMap e.1 e.2 (ε • N e.1) (ε • N e.2) p =
      stripMap e.1 e.2 (ε • N e.1) (ε • N e.2) q →
    p = q ∨ (e.1 ∈ H ∧ p.1 = 0 ∧ q.1 = 0) ∨ (e.2 ∈ H ∧ p.1 = 1 ∧ q.1 = 1)) ∧
  (∀ e ∈ S, ∀ f ∈ S, StripCentersAgree e.1 e.2 (ε • N e.1) (ε • N e.2)
    f.1 f.2 (ε • N f.1) (ε • N f.2)) ∧
  (∀ e ∈ S, ∀ X ∈ H, ∀ p : I × I,
    stripMap e.1 e.2 (ε • N e.1) (ε • N e.2) p = X →
      AffineMap.lineMap e.1 e.2 (p.1 : ℝ) = X)

/-- All three properties hold simultaneously for every sufficiently small
positive width, as a consequence of actual finite segment geometry. -/
theorem eventually_good_strip_width (S : Finset (Plane × Plane)) (H : Set Plane)
    (hH : H.Finite) (N : Plane → Plane)
    (hcorner : TwoValentCorners (S : Set (Plane × Plane)) H)
    (hpair : EndpointIntersections (S : Set (Plane × Plane)))
    (hne : ∀ e ∈ S, e.1 ≠ e.2)
    (hvertex : HostEndpointOnly (S : Set (Plane × Plane)) H)
    (hzero : ∀ x ∈ H, N x = 0)
    (hout : ∀ a b, (a, b) ∈ S → a ∉ H → 0 < cross (b - a) (N a))
    (hin : ∀ a b, (a, b) ∈ S → b ∉ H → 0 < cross (b - a) (N b))
    (hfree : ∀ a b, (a, b) ∈ S → a ∉ H ∨ b ∉ H) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, GoodStripWidth S H N ε := by
  exact (eventually_all_strip_self_equalities S H N hzero hout hin hfree).and
    ((eventually_all_strip_centers_agree S H N hcorner hpair hne hzero hout hin hfree).and
      (eventually_all_strips_respect_hosts S H hH N hvertex hzero hout hin hfree))

/-- Construct both the global normals and an actual common positive width below
any prescribed bound. Every local geometric property is proved, not assumed. -/
theorem exists_normal_and_good_width (S : Finset (Plane × Plane)) (H : Set Plane)
    (hH : H.Finite) (hcorner : TwoValentCorners (S : Set (Plane × Plane)) H)
    (hpair : EndpointIntersections (S : Set (Plane × Plane)))
    (hne : ∀ e ∈ S, e.1 ≠ e.2)
    (hvertex : HostEndpointOnly (S : Set (Plane × Plane)) H)
    (hfree : ∀ a b, (a, b) ∈ S → a ∉ H ∨ b ∉ H) (η : ℝ) (hη : 0 < η) :
    ∃ (N : Plane → Plane) (ε : ℝ), (∀ x ∈ H, N x = 0) ∧
      0 < ε ∧ ε < η ∧ GoodStripWidth S H N ε := by
  obtain ⟨N, hzero, hout, hin⟩ := exists_normal_assignment (S : Set (Plane × Plane)) H hcorner
  have hgood := eventually_good_strip_width S H hH N hcorner hpair hne hvertex hzero hout hin hfree
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ε < η :=
    ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).eventually_lt_const hη).filter_mono
      nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hsmall, hgood⟩ := (hpos.and (hsmall.and hgood)).exists
  exact ⟨N, ε, hzero, hε, hsmall, hgood⟩

end PlanarHom.Polygonal
