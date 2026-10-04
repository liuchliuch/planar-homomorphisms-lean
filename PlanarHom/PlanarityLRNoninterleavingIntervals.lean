import PlanarHom.PlanarityLRRealizationArches

/-! NEW algebraic bridge from non-alternation of distinct ports to the exact
strict interval condition consumed by the literal circle routing. -/
namespace PlanarHom.PlanarityLRRealization

theorem noninterleaving_of_not_alternating {a b c d : ℝ}
    (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d)
    (h₁ : ¬(a<c ∧ c<b ∧ b<d)) (h₂ : ¬(c<a ∧ a<d ∧ d<b)) :
    Noninterleaving a b c d := by
  rcases lt_or_gt_of_ne hac with hac | hca
  · by_cases h : b<c
    · exact Or.inl h
    · have hcb : c<b := lt_of_le_of_ne (le_of_not_gt h) hbc.symm
      by_cases hdb : d<b
      · exact Or.inr (Or.inr (Or.inl ⟨hac,hdb⟩))
      · have hbd' : b<d := lt_of_le_of_ne (le_of_not_gt hdb) hbd
        exact False.elim (h₁ ⟨hac,hcb,hbd'⟩)
  · by_cases h : d<a
    · exact Or.inr (Or.inl h)
    · have had' : a<d := lt_of_le_of_ne (le_of_not_gt h) had
      by_cases hbd' : b<d
      · exact Or.inr (Or.inr (Or.inr ⟨hca,hbd'⟩))
      · have hdb : d<b := lt_of_le_of_ne (le_of_not_gt hbd') hbd.symm
        exact False.elim (h₂ ⟨hca,had',hdb⟩)

theorem Noninterleaving.not_alternating {a b c d : ℝ} (h : Noninterleaving a b c d) :
    ¬(a<c ∧ c<b ∧ b<d) ∧ ¬(c<a ∧ a<d ∧ d<b) := by
  rcases h with h | h | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> constructor <;> rintro ⟨_,_,_⟩ <;> linarith

theorem noninterleaving_iff_not_alternating {a b c d : ℝ}
    (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) :
    Noninterleaving a b c d ↔ ¬(a<c ∧ c<b ∧ b<d) ∧ ¬(c<a ∧ a<d ∧ d<b) :=
  ⟨Noninterleaving.not_alternating,fun h => noninterleaving_of_not_alternating hac had hbc hbd h.1 h.2⟩

end PlanarHom.PlanarityLRRealization
