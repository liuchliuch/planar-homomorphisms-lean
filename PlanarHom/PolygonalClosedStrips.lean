import PlanarHom.PolygonalTubeSeparation

/-!
# Closed-strip equality classification

The local strip API includes the boundary parameters used by global polygonal
concatenation. Equality forces equal square parameters, except that a genuinely
pinched endpoint side may collapse to its endpoint vertex.
-/

noncomputable section
open Set unitInterval Filter
open scoped Topology
namespace PlanarHom.Polygonal
open MultiGraph

/-- A nonzero mixed determinant at the compared parameters already forces
parameter equality; no interior restriction is required in this algebraic lemma. -/
theorem stripMap_injective_of_mixed_cross_ne (P Q A B : Plane) (p q : I × I)
    (hcross : cross (Q - P + (p.2 : ℝ) • (B - A)) (A + (q.1 : ℝ) • (B - A)) ≠ 0)
    (heq : stripMap P Q A B p = stripMap P Q A B q) : p = q := by
  let D := Q - P + (p.2 : ℝ) • (B - A)
  let N := A + (q.1 : ℝ) • (B - A)
  have hz : ((p.1 : ℝ) - (q.1 : ℝ)) • D + ((p.2 : ℝ) - (q.2 : ℝ)) • N = 0 := by
    rw [← strip_sub]
    exact sub_eq_zero.mpr heq
  have ht : ((p.1 : ℝ) - (q.1 : ℝ)) * cross D N = 0 := by
    simpa using congrArg (fun W => cross W N) hz
  have hs : ((p.2 : ℝ) - (q.2 : ℝ)) * cross D N = 0 := by
    simpa using congrArg (fun W => cross D W) hz
  apply Prod.ext <;> apply Subtype.ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hcross)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hcross)

/-- Four strictly positive corner determinants give injectivity on the entire
closed square, including both transverse boundary sides. -/
theorem stripMap_injective_closed (P Q A B : Plane)
    (h00 : 0 < cross (Q - P) A) (h10 : 0 < cross (Q - P) B)
    (h01 : 0 < cross (Q - P + (B - A)) A)
    (h11 : 0 < cross (Q - P + (B - A)) B) : Function.Injective (stripMap P Q A B) := by
  intro p q heq
  apply stripMap_injective_of_mixed_cross_ne P Q A B p q ?_ heq
  apply ne_of_gt
  rw [cross_strip_corners]
  exact closed_combo_pos
    (closed_combo_pos h00 h10 q.1.2.1 q.1.2.2)
    (closed_combo_pos h01 h11 q.1.2.1 q.1.2.2) p.2.2.1 p.2.2.2

/-- A positive second longitudinal parameter suffices for injectivity against
any parameter in an initially pinched closed strip. -/
theorem pinched_start_eq_of_pos (P Q B : Plane) (hB : 0 < cross (Q - P) B)
    (p q : I × I) (hq : 0 < (q.1 : ℝ))
    (heq : stripMap P Q 0 B p = stripMap P Q 0 B q) : p = q := by
  apply stripMap_injective_of_mixed_cross_ne P Q 0 B p q ?_ heq
  apply ne_of_gt
  simpa using mul_pos hq hB

/-- The corresponding statement at a pinched terminal side. -/
theorem pinched_end_eq_of_lt_one (P Q A : Plane) (hA : 0 < cross (Q - P) A)
    (p q : I × I) (hq : (q.1 : ℝ) < 1)
    (heq : stripMap P Q A 0 p = stripMap P Q A 0 q) : p = q := by
  apply stripMap_injective_of_mixed_cross_ne P Q A 0 p q ?_ heq
  apply ne_of_gt
  have he : cross (Q - P + (p.2 : ℝ) • (0 - A)) (A + (q.1 : ℝ) • (0 - A)) =
      (1 - (q.1 : ℝ)) * cross (Q - P) A := by
    simp only [zero_sub, cross_add_left, cross_add_right, cross_smul_left,
      cross_smul_right, cross_neg_left, cross_neg_right, cross_self]
    ring
  rw [he]
  exact mul_pos (by linarith) hA

/-- All equalities in an initially pinched strip are either genuine square
parameter equality or collapse on the initial endpoint side. -/
theorem pinched_start_eq_or_endpoint (P Q B : Plane) (hB : 0 < cross (Q - P) B)
    (p q : I × I) (heq : stripMap P Q 0 B p = stripMap P Q 0 B q) :
    p = q ∨ (p.1 = 0 ∧ q.1 = 0) := by
  by_cases hq : q.1 = 0
  · by_cases hp : p.1 = 0
    · exact Or.inr ⟨hp, hq⟩
    · apply Or.inl
      apply Eq.symm
      apply pinched_start_eq_of_pos P Q B hB q p ?_ heq.symm
      have hn : (p.1 : ℝ) ≠ 0 := fun h => hp (Subtype.ext h)
      exact lt_of_le_of_ne p.1.2.1 hn.symm
  · apply Or.inl
    apply pinched_start_eq_of_pos P Q B hB p q ?_ heq
    have hn : (q.1 : ℝ) ≠ 0 := fun h => hq (Subtype.ext h)
    exact lt_of_le_of_ne q.1.2.1 hn.symm

/-- All equalities in a terminally pinched strip have the analogous classification. -/
theorem pinched_end_eq_or_endpoint (P Q A : Plane) (hA : 0 < cross (Q - P) A)
    (p q : I × I) (heq : stripMap P Q A 0 p = stripMap P Q A 0 q) :
    p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  by_cases hq : q.1 = 1
  · by_cases hp : p.1 = 1
    · exact Or.inr ⟨hp, hq⟩
    · apply Or.inl
      apply Eq.symm
      apply pinched_end_eq_of_lt_one P Q A hA q p ?_ heq.symm
      have hn : (p.1 : ℝ) ≠ 1 := fun h => hp (Subtype.ext h)
      exact lt_of_le_of_ne p.1.2.2 hn
  · apply Or.inl
    apply pinched_end_eq_of_lt_one P Q A hA p q ?_ heq
    have hn : (q.1 : ℝ) ≠ 1 := fun h => hq (Subtype.ext h)
    exact lt_of_le_of_ne q.1.2.2 hn

/-- The full local equality classification for small widths, with zero normal
vectors explicitly marking exactly the possible collapsed endpoint sides. -/
theorem eventually_strip_eq_or_pinched_endpoint (P Q A B : Plane)
    (hA : A = 0 ∨ 0 < cross (Q - P) A)
    (hB : B = 0 ∨ 0 < cross (Q - P) B) (hne : A ≠ 0 ∨ B ≠ 0) :
    ∀ᶠ ε : ℝ in 𝓝[Set.Ioi 0] 0, ∀ p q : I × I,
      stripMap P Q (ε • A) (ε • B) p = stripMap P Q (ε • A) (ε • B) q →
      p = q ∨ (A = 0 ∧ p.1 = 0 ∧ q.1 = 0) ∨ (B = 0 ∧ p.1 = 1 ∧ q.1 = 1) := by
  rcases hA with rfl | hA
  · rcases hB with rfl | hB
    · simp only [ne_self_iff_false, or_self] at hne
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro p q heq
      have hB' : 0 < cross (Q - P) (ε • B) := by
        simpa using mul_pos (show 0 < ε from hε) hB
      rcases pinched_start_eq_or_endpoint P Q (ε • B) hB' p q (by simpa using heq) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · rcases hB with rfl | hB
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro p q heq
      have hA' : 0 < cross (Q - P) (ε • A) := by
        simpa using mul_pos (show 0 < ε from hε) hA
      rcases pinched_end_eq_or_endpoint P Q (ε • A) hA' p q (by simpa using heq) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · filter_upwards [eventually_corner_positive P Q A B hA hB] with ε hε
      intro p q heq
      exact Or.inl (stripMap_injective_closed P Q (ε • A) (ε • B)
        hε.1 hε.2.1 hε.2.2.1 hε.2.2.2 heq)

end PlanarHom.Polygonal
