import PlanarHom.ColoringWireMacroTyped
import PlanarHom.ColoringConnectedMacroSemantics
import PlanarHom.ColoringIncidenceTransport

noncomputable section
open Classical
namespace PlanarHom.ColoringWireMacroSemantics
open MultiGraph ThreeColorPaletteCounting ColoringPaletteNetwork
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate ColoringTemplateBoundaryStates
open PalettedColoringPatches
open ColoringWireMacroTyped

def sourceEquiv : Solutions occurrence ≃ SourceSolutions equality where
  toFun a := ⟨a.val,by
    exact (ColoringWireMacroCore.source_spec a.val).mp a.property⟩
  invFun a := ⟨a.val,by
    exact (ColoringWireMacroCore.source_spec a.val).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def accepted := Allowed equality 2 (by decide) (by decide)
def bitsEquiv : Solutions occurrence ≃ {b : Fin 2 → Bool // accepted b} :=
  sourceEquiv.trans (boundaryEquiv equality 2 (by decide) (by decide))

theorem bits_port (b : {b : Fin 2 → Bool // accepted b}) (p : Fin 2) :
    (bitsEquiv.symm b).val (portVariable p)=b.val p := by
  exact boundaryEquiv_symm_port equality 2 (by decide) (by decide) b p

def typedEquiv : Coloring graph ≃ State (Fin 2) accepted :=
  ColoringConnectedMacroSemantics.equiv occurrence left right shape source
    ColoringWireMacroCore.cover ColoringWireMacroCore.coherent (component left right 0) accepted bitsEquiv

theorem typed_inverse_port (s : State (Fin 2) accepted) (p : Fin 2) (k : Fin 3) :
    (typedEquiv.symm s).val (boundary p k)=portColor s (p,k) := by
  fin_cases k
  · exact ColoringConnectedMacroSemantics.inverse_primary occurrence left right shape source
      ColoringWireMacroCore.cover ColoringWireMacroCore.coherent (component left right 0) accepted bitsEquiv
      portVariable bits_port s p
  · exact ColoringConnectedMacroSemantics.inverse_gray occurrence left right shape source
      ColoringWireMacroCore.cover ColoringWireMacroCore.coherent (component left right 0) accepted bitsEquiv s p
  · exact ColoringConnectedMacroSemantics.inverse_black occurrence left right shape source
      ColoringWireMacroCore.cover ColoringWireMacroCore.coherent (component left right 0) accepted bitsEquiv s p

def numericEquiv : Coloring ColoringWireMacroCoordinates.graph ≃ State (Fin 2) accepted :=
  ColoringWireMacroTyped.numericEquiv.colorings.symm.trans typedEquiv

theorem numeric_inverse_port (s : State (Fin 2) accepted) (p : Fin 2) (k : Fin 3) :
    (numericEquiv.symm s).val (boundaryIds p k)=portColor s (p,k) := by
  change (typedEquiv.symm s).val (number.symm (boundaryIds p k))=_
  rw [←boundary_number,Equiv.symm_apply_apply]
  exact typed_inverse_port s p k

end PlanarHom.ColoringWireMacroSemantics
