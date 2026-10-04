import PlanarHom.PlanarityLRDirect
import Mathlib.Data.List.Lex

/-! NEW reconstruction. The actual DFS back-event word comparator is a total,
transitive, antisymmetric order with literal occurrence-index tie-breaking. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity

 theorem eventLE_iff (g : MixedCode) (bits : List Bool) (a b : ℕ) :
    eventLE g bits a b=true ↔ backWord g bits a<backWord g bits b ∨
      backWord g bits a=backWord g bits b ∧ a≤b := by
  simp [eventLE,List.lex_eq_true_iff_lt]

 theorem eventLE_total (g : MixedCode) (bits : List Bool) (a b : ℕ) :
    (eventLE g bits a b || eventLE g bits b a)=true := by
  rw [Bool.or_eq_true,eventLE_iff,eventLE_iff]
  rcases lt_trichotomy (backWord g bits a) (backWord g bits b) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total a b with hab | hba
    · exact Or.inl (Or.inr ⟨h,hab⟩)
    · exact Or.inr (Or.inr ⟨h.symm,hba⟩)
  · exact Or.inr (Or.inl h)

 theorem eventLE_trans (g : MixedCode) (bits : List Bool) (a b c : ℕ)
    (hab : eventLE g bits a b=true) (hbc : eventLE g bits b c=true) : eventLE g bits a c=true := by
  rw [eventLE_iff] at hab hbc ⊢
  rcases hab with hab | ⟨hab,hab'⟩ <;> rcases hbc with hbc | ⟨hbc,hbc'⟩
  · exact Or.inl (lt_trans hab hbc)
  · exact Or.inl (hbc ▸ hab)
  · exact Or.inl (hab ▸ hbc)
  · exact Or.inr ⟨hab.trans hbc,hab'.trans hbc'⟩

 theorem eventLE_antisymm (g : MixedCode) (bits : List Bool) (a b : ℕ)
    (hab : eventLE g bits a b=true) (hba : eventLE g bits b a=true) : a=b := by
  rw [eventLE_iff] at hab hba
  rcases hab with hab | ⟨hab,hab'⟩ <;> rcases hba with hba | ⟨hba,hba'⟩
  · exact (lt_asymm hab hba).elim
  · exact (lt_irrefl _ (hba ▸ hab)).elim
  · exact (lt_irrefl _ (hab ▸ hba)).elim
  · exact Nat.le_antisymm hab' hba'

end PlanarHom.PlanarityLRDirect
