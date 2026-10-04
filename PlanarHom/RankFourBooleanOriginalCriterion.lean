import PlanarHom.RankFourBooleanFactors

noncomputable section
namespace PlanarHom.RankFour

def OriginalBooleanEquations (A:Matrix Bool Bool ℝ) : Prop :=
  A false false*A true true=A false true^2 ∨ A false true=0 ∨
  A false false=A true true ∨
  (A false false*A true true= -(A false true^2) ∧ A false false= -A true true)

theorem booleanEasy_iff_original (A:Matrix Bool Bool ℝ) : BooleanEasy A ↔
    (∀i j,A i j=A j i) ∧ (∀i j,0≤A i j) ∧ OriginalBooleanEquations A := by
  constructor
  · rintro ⟨hs,hn,h⟩
    refine ⟨hs,hn,?_⟩
    rcases h with h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · rintro ⟨hs,hn,h⟩
    refine ⟨hs,hn,?_⟩
    rcases h with h|h|h|⟨h,h'⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact .inr (.inr (by linarith [hn false false,hn true true]))

end PlanarHom.RankFour
