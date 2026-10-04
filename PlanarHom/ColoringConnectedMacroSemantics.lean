import PlanarHom.ColoringExposedPaletteNetwork
import PlanarHom.ColoringTemplateBoundaryStates
import PlanarHom.PalettedColoringPatches

/-! A connected palette-link network has one freely chosen palette. This
packages its proved actual coloring equivalence with any proved boundary-state
bijection, retaining the literal three colors at every exposed port. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringConnectedMacroSemantics
open MultiGraph ThreeColorPaletteCounting PlanarColoringClause
open ColoringPaletteNetwork ColoringExposedPaletteNetwork ColoringPalettePairCopy
open PalettedColoringPatches
variable {V C L P : Type} (occurrence : C → Fin 3 → V)
variable (left right : L → C × Fin 3) (shape : P → Shape) (source : P → C × Fin 3)
variable (cover : ∀ v,∃ c k,occurrence c k=v) (coherent : Coherent occurrence left right)
variable [Subsingleton (Component left right)] (root : Component left right)
variable (accepted : (P → Bool) → Prop)
variable (bitsEquiv : Solutions occurrence ≃ {b : P → Bool // accepted b})
variable (portVariable : P → V)
variable (bits_port : ∀ b p,(bitsEquiv.symm b).val (portVariable p)=b.val p)

def paletteEquiv : (Component left right → Palette) ≃ Palette where
  toFun f := f root
  invFun p := fun _ => p
  left_inv f := funext fun q => congrArg f (Subsingleton.elim root q)
  right_inv _ := rfl

def equiv : Coloring (graph occurrence left right shape source) ≃ State P accepted :=
  (componentEquiv occurrence left right shape source cover coherent).trans
    (Equiv.prodCongr (paletteEquiv left right root) bitsEquiv)

include bits_port in
theorem inverse_primary (s : State P accepted) (p : P) :
    ((equiv occurrence left right shape source cover coherent root accepted bitsEquiv).symm s).val
      (primary shape (portVariable p))=palettePermutation s.1 (boolColor (s.2.val p)) := by
  change ((componentEquiv occurrence left right shape source cover coherent).symm
    ((fun _ => s.1),bitsEquiv.symm s.2)).val _=_
  rw [componentEquiv_symm_primary,bits_port]

theorem inverse_gray (s : State P accepted) (p : P) :
    ((equiv occurrence left right shape source cover coherent root accepted bitsEquiv).symm s).val
      (grayPort shape p)=s.1.val.2 := by
  change ((componentEquiv occurrence left right shape source cover coherent).symm
    ((fun _ => s.1),bitsEquiv.symm s.2)).val _=_
  rw [componentEquiv_symm_gray]

theorem inverse_black (s : State P accepted) (p : P) :
    ((equiv occurrence left right shape source cover coherent root accepted bitsEquiv).symm s).val
      (blackPort shape p)=s.1.val.1 := by
  change ((componentEquiv occurrence left right shape source cover coherent).symm
    ((fun _ => s.1),bitsEquiv.symm s.2)).val _=_
  rw [componentEquiv_symm_black]

end PlanarHom.ColoringConnectedMacroSemantics
