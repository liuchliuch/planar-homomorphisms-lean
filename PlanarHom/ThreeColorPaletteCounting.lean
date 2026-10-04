import PlanarHom.PlanarColoringExclusiveCrossing

/-! Exact labeled-color multiplicity for a pinned three-color reference palette.
A pair forced to distinct colors contributes exactly six ordinary colorings;
this factor is retained rather than quotienting solutions by color isomorphism. -/
noncomputable section
open Classical
namespace PlanarHom.ThreeColorPaletteCounting
open MultiGraph
set_option synthInstance.maxSize 10000

def paletteMap (a b : Fin 3) : Fin 3 → Fin 3 := ![a,b,PlanarColoringExclusiveCrossing.third a b]

theorem paletteMap_injective (a b : Fin 3) (hab : a≠b) : Function.Injective (paletteMap a b) := by
  have h : ∀ a b : Fin 3, a≠b → Function.Injective (paletteMap a b) := by
    unfold Function.Injective paletteMap PlanarColoringExclusiveCrossing.third
    decide
  exact h a b hab

def paletteEquiv (a b : Fin 3) (hab : a≠b) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (paletteMap a b) ⟨paletteMap_injective a b hab,Finite.surjective_of_injective (paletteMap_injective a b hab)⟩

@[simp] theorem paletteEquiv_zero (a b : Fin 3) (h : a≠b) : paletteEquiv a b h 0=a := rfl
@[simp] theorem paletteEquiv_one (a b : Fin 3) (h : a≠b) : paletteEquiv a b h 1=b := rfl

abbrev Coloring {V E : Type} (G : MultiGraph V E) := {col : V → Fin 3 // ∀ e,col (G.src e)≠col (G.dst e)}
abbrev PinnedColoring {V E : Type} (G : MultiGraph V E) (black gray : V) :=
  {col : V → Fin 3 // (∀ e,col (G.src e)≠col (G.dst e)) ∧ col black=0 ∧ col gray=1}
abbrev Palette := {p : Fin 3 × Fin 3 // p.1≠p.2}

/-- Recoloring by a true permutation preserves every actual edge inequality. -/
theorem proper_recolor {V E : Type} (G : MultiGraph V E) (col : V → Fin 3)
    (p : Equiv.Perm (Fin 3)) :
    (∀ e,p (col (G.src e))≠p (col (G.dst e))) ↔ (∀ e,col (G.src e)≠col (G.dst e)) := by
  simp only [ne_eq,p.injective.eq_iff]

/-- A genuine bijection accounts for the six palettes whenever the graph
itself forces its two reference vertices to have distinct colors. -/
def coloringEquiv {V E : Type} (G : MultiGraph V E) (black gray : V)
    (hsep : ∀ col : Coloring G,col.val black≠col.val gray) :
    Coloring G ≃ Palette × PinnedColoring G black gray where
  toFun col :=
    let p : Palette := ⟨(col.val black,col.val gray),hsep col⟩
    let eqv := paletteEquiv p.val.1 p.val.2 p.property
    (p,⟨eqv.symm ∘ col.val,⟨
      (proper_recolor G col.val eqv.symm).mpr col.property,
      by change eqv.symm (col.val black)=0; exact eqv.symm_apply_eq.mpr rfl,
      by change eqv.symm (col.val gray)=1; exact eqv.symm_apply_eq.mpr rfl⟩⟩)
  invFun pair :=
    ⟨paletteEquiv pair.1.val.1 pair.1.val.2 pair.1.property ∘ pair.2.val,
      (proper_recolor G pair.2.val _).mpr pair.2.property.1⟩
  left_inv col := by
    apply Subtype.ext
    funext v
    exact Equiv.apply_symm_apply _ _
  right_inv pair := by
    rcases pair with ⟨⟨⟨a,b⟩,hab⟩,⟨col,hcol,hb,hg⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [Function.comp_apply,hb,hg]
    · apply Subtype.ext
      funext v
      change (paletteEquiv ((paletteEquiv a b hab) (col black))
        ((paletteEquiv a b hab) (col gray)) _).symm ((paletteEquiv a b hab) (col v))=col v
      simp only [hb,hg,paletteEquiv_zero,paletteEquiv_one,Equiv.symm_apply_apply]

theorem palette_card : Fintype.card Palette=6 := by decide

/-- The natural three-coloring count is six times the pinned count. -/
theorem coloring_card {V E : Type} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (black gray : V)
    (hsep : ∀ col : Coloring G,col.val black≠col.val gray) :
    ProperColoringPottsReduction.properColoringCount G 3=
      6*Fintype.card (PinnedColoring G black gray) := by
  rw [ProperColoringPottsReduction.properColoringCount,Fintype.card_congr (coloringEquiv G black gray hsep),
    Fintype.card_prod,palette_card]


/-- A representation-independent cardinal form prevents a concrete gadget's
finite assignment table from being unfolded during downstream conversion. -/
theorem properCount_eq_natCard {V E : Type} [Fintype V] [Fintype E] (G : MultiGraph V E) :
    ProperColoringPottsReduction.properColoringCount G 3=Nat.card (Coloring G) := by
  rw [Nat.card_eq_fintype_card]
  rfl

end PlanarHom.ThreeColorPaletteCounting
