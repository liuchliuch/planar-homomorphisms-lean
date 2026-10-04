import PlanarHom.ColoringFanMacroTyped
import PlanarHom.ColoringConnectedMacroSemantics
import PlanarHom.ColoringIncidenceTransport

noncomputable section
open Classical
namespace PlanarHom.ColoringFanMacroSemantics
open MultiGraph ThreeColorPaletteCounting ColoringPaletteNetwork
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate ColoringTemplateBoundaryStates
open PalettedColoringPatches
open ColoringFanMacroTyped

def sourceEquiv : Solutions occurrence ≃ SourceSolutions fanout where
  toFun a := ⟨a.val,by
    exact (ColoringFanMacroCore.source_spec a.val).mp a.property⟩
  invFun a := ⟨a.val,by
    exact (ColoringFanMacroCore.source_spec a.val).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def accepted := Allowed fanout 3 (by decide) (by decide)
def bitsEquiv : Solutions occurrence ≃ {b : Fin 3 → Bool // accepted b} :=
  sourceEquiv.trans (boundaryEquiv fanout 3 (by decide) (by decide))

theorem bits_port (b : {b : Fin 3 → Bool // accepted b}) (p : Fin 3) :
    (bitsEquiv.symm b).val (portVariable p)=b.val p := by
  exact boundaryEquiv_symm_port fanout 3 (by decide) (by decide) b p

def typedEquiv : Coloring graph ≃ State (Fin 3) accepted :=
  ColoringConnectedMacroSemantics.equiv occurrence left right shape source
    ColoringFanMacroCore.cover ColoringFanMacroCore.coherent (component left right 0) accepted bitsEquiv

theorem typed_inverse_port (s : State (Fin 3) accepted) (p : Fin 3) (k : Fin 3) :
    (typedEquiv.symm s).val (boundary p k)=portColor s (p,k) := by
  fin_cases k
  · exact ColoringConnectedMacroSemantics.inverse_primary occurrence left right shape source
      ColoringFanMacroCore.cover ColoringFanMacroCore.coherent (component left right 0) accepted bitsEquiv
      portVariable bits_port s p
  · exact ColoringConnectedMacroSemantics.inverse_gray occurrence left right shape source
      ColoringFanMacroCore.cover ColoringFanMacroCore.coherent (component left right 0) accepted bitsEquiv s p
  · exact ColoringConnectedMacroSemantics.inverse_black occurrence left right shape source
      ColoringFanMacroCore.cover ColoringFanMacroCore.coherent (component left right 0) accepted bitsEquiv s p

def numericEquiv : Coloring ColoringFanMacroCoordinates.graph ≃ State (Fin 3) accepted :=
  ColoringFanMacroTyped.numericEquiv.colorings.symm.trans typedEquiv

theorem numeric_inverse_port (s : State (Fin 3) accepted) (p : Fin 3) (k : Fin 3) :
    (numericEquiv.symm s).val (boundaryIds p k)=portColor s (p,k) := by
  change (typedEquiv.symm s).val (number.symm (boundaryIds p k))=_
  rw [←boundary_number,Equiv.symm_apply_apply]
  exact typed_inverse_port s p k

end PlanarHom.ColoringFanMacroSemantics
