import PlanarHom.PlanarColoringClauseSemantics
import PlanarHom.ThreeColorPaletteCounting

/-! Explicit bijections and exact labeled-color counts for the actual clause
coloring graph. The six reference palettes remain part of the natural count. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarColoringClause
open ParsimoniousNorOneInThree
set_option maxHeartbeats 5000000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 20000

abbrev Accepted := {b : Fin 3 → Bool // ExactlyOne (b 0) (b 1) (b 2)}

def hot (k : Fin 3) : Fin 3 → Bool := fun i => decide (i=k)
def hotIndex (b : Fin 3 → Bool) : Fin 3 := if b 0 then 0 else if b 1 then 1 else 2

theorem hot_accepted (k : Fin 3) : ExactlyOne (hot k 0) (hot k 1) (hot k 2) := by
  fin_cases k <;> simp [ExactlyOne,hot]

theorem hotIndex_hot (k : Fin 3) : hotIndex (hot k)=k := by fin_cases k <;> rfl

theorem hot_hotIndex (b : Fin 3 → Bool) (hb : ExactlyOne (b 0) (b 1) (b 2)) : hot (hotIndex b)=b := by
  funext i
  fin_cases i
  all_goals cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    simp [hot,hotIndex,ExactlyOne,h0,h1,h2] at hb ⊢

def acceptedEquiv : Accepted ≃ Fin 3 where
  toFun b := hotIndex b.val
  invFun k := ⟨hot k,hot_accepted k⟩
  left_inv b := Subtype.ext (hot_hotIndex b.val b.property)
  right_inv := hotIndex_hot

def pinnedEquiv : ThreeColorPaletteCounting.PinnedColoring graph (copyVertex 0 7) (copyVertex 0 6) ≃ Accepted where
  toFun col := ⟨inputBits col.val,((proper_pinned_iff col.val).mp col.property).1⟩
  invFun b := ⟨extension b.val,
    (proper_pinned_iff _).mpr ⟨by simpa only [inputBits_extension] using b.property,
      by rw [inputBits_extension]⟩⟩
  left_inv col := Subtype.ext (((proper_pinned_iff col.val).mp col.property).2.symm)
  right_inv b := Subtype.ext (inputBits_extension b.val)

theorem palette_separated (col : ThreeColorPaletteCounting.Coloring graph) :
    col.val (copyVertex 0 7)≠col.val (copyVertex 0 6) :=
  (PlanarColoringOneWayConverter.palette_copy (col.val ∘ copyVertex 0)
    (((proper_split col.val).mp col.property).1 0)).2.2

def totalEquiv : ThreeColorPaletteCounting.Coloring graph ≃ ThreeColorPaletteCounting.Palette × Fin 3 :=
  (ThreeColorPaletteCounting.coloringEquiv graph (copyVertex 0 7) (copyVertex 0 6) palette_separated).trans
    ((Equiv.refl _).prodCongr (pinnedEquiv.trans acceptedEquiv))

theorem pinned_count : Nat.card (ThreeColorPaletteCounting.PinnedColoring graph (copyVertex 0 7) (copyVertex 0 6))=3 :=
  (Nat.card_congr (pinnedEquiv.trans acceptedEquiv)).trans (by simp)

theorem coloring_count : ProperColoringPottsReduction.properColoringCount graph 3=18 := by
  rw [ThreeColorPaletteCounting.properCount_eq_natCard]
  exact (Nat.card_congr totalEquiv).trans (by rw [Nat.card_eq_fintype_card]; decide)

end PlanarHom.PlanarColoringClause
