import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! NEW four-port order implication used in LR necessity. A deeper return
target lies within an ancestor interval containing both branch sources, while
the shallower return target lies outside that interval. Nonalternation then
forces the deeper return onto the side fixed by branch order. -/
namespace PlanarHom.PlanarityLRNecessity
variable {E : Type*}

def PairNonalternating (rank : E × Bool → ℕ) (b c : E) : Prop :=
  ∀ s t, (¬ (rank (b,s)<rank (c,t) ∧ rank (c,t)<rank (b,!s) ∧ rank (b,!s)<rank (c,!t))) ∧
    (¬ (rank (c,t)<rank (b,s) ∧ rank (b,s)<rank (c,!t) ∧ rank (c,!t)<rank (b,!s)))

/-- The incoming endpoint of b must be before its source exactly when b's
outgoing branch is before c's outgoing branch. All conclusions are literal
inequalities on the original paired occurrence ranks. -/
theorem forcedSide_of_nestedCuts (rank : E × Bool → ℕ) (b c : E)
    (hnonalt : PairNonalternating rank b c)
    (hsources : rank (b,true)≠rank (c,true))
    (hinner : (rank (b,false)<rank (b,true) ∧ rank (b,false)<rank (c,true)) ∨
      (rank (b,true)<rank (b,false) ∧ rank (c,true)<rank (b,false)))
    (houter : (rank (c,false)<rank (b,false) ∧ rank (c,false)<rank (b,true) ∧ rank (c,false)<rank (c,true)) ∨
      (rank (b,false)<rank (c,false) ∧ rank (b,true)<rank (c,false) ∧ rank (c,true)<rank (c,false))) :
    decide (rank (b,true)<rank (b,false))=decide (rank (c,true)<rank (b,true)) := by
  rcases lt_or_gt_of_ne hsources with hbc | hcb
  · have hbefore : rank (b,false)<rank (b,true) := by
      rcases hinner with h | h
      · exact h.1
      · rcases houter with ho | ho
        · exact False.elim ((hnonalt true false).2 ⟨ho.2.1,hbc,h.2⟩)
        · exact False.elim ((hnonalt true true).1 ⟨hbc,h.2,ho.1⟩)
    simp only [decide_eq_false (not_lt_of_ge hbefore.le),decide_eq_false (not_lt_of_ge hbc.le)]
  · have hafter : rank (b,true)<rank (b,false) := by
      rcases hinner with h | h
      · rcases houter with ho | ho
        · exact False.elim ((hnonalt false false).2 ⟨ho.1,h.2,hcb⟩)
        · exact False.elim ((hnonalt false true).1 ⟨h.2,hcb,ho.2.1⟩)
      · exact h.1
    simp only [decide_eq_true hafter,decide_eq_true hcb]

/-- The three-point outer cut follows from the ordinary two-point infix
separation law, with one common interior rank preventing inconsistent sides. -/
theorem three_inside_of_pairwise_outside {a b c x : ℕ}
    (hab : (x<a ∧ x<b) ∨ (a<x ∧ b<x))
    (hbc : (x<b ∧ x<c) ∨ (b<x ∧ c<x)) :
    (x<a ∧ x<b ∧ x<c) ∨ (a<x ∧ b<x ∧ c<x) := by
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · exact Or.inl ⟨hab.1,hab.2,hbc.2⟩
  · omega
  · omega
  · exact Or.inr ⟨hab.1,hab.2,hbc.2⟩

end PlanarHom.PlanarityLRNecessity
