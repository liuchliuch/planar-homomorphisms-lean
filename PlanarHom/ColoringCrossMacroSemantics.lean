import PlanarHom.ColoringCrossMacroTyped
import PlanarHom.ColoringConnectedMacroSemantics
import PlanarHom.ColoringIncidenceTransport

noncomputable section
open Classical
namespace PlanarHom.ColoringCrossMacroSemantics
open MultiGraph ThreeColorPaletteCounting ColoringPaletteNetwork
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate ColoringTemplateBoundaryStates
open PalettedColoringPatches
open ColoringCrossMacroTyped

def sourceEquiv : Solutions occurrence ≃ SourceSolutions crossover where
  toFun a := ⟨a.val,by
    exact (ColoringCrossMacroCore.source_spec a.val).mp a.property⟩
  invFun a := ⟨a.val,by
    exact (ColoringCrossMacroCore.source_spec a.val).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def accepted := Allowed crossover 4 (by decide) (by decide)
def bitsEquiv : Solutions occurrence ≃ {b : Fin 4 → Bool // accepted b} :=
  sourceEquiv.trans (boundaryEquiv crossover 4 (by decide) (by decide))

theorem bits_port (b : {b : Fin 4 → Bool // accepted b}) (p : Fin 4) :
    (bitsEquiv.symm b).val (portVariable p)=b.val p := by
  exact boundaryEquiv_symm_port crossover 4 (by decide) (by decide) b p

def typedEquiv : Coloring graph ≃ State (Fin 4) accepted :=
  ColoringConnectedMacroSemantics.equiv occurrence left right shape source
    ColoringCrossMacroCore.cover ColoringCrossMacroCore.coherent (component left right 0) accepted bitsEquiv

theorem typed_inverse_port (s : State (Fin 4) accepted) (p : Fin 4) (k : Fin 3) :
    (typedEquiv.symm s).val (boundary p k)=portColor s (p,k) := by
  fin_cases k
  · exact ColoringConnectedMacroSemantics.inverse_primary occurrence left right shape source
      ColoringCrossMacroCore.cover ColoringCrossMacroCore.coherent (component left right 0) accepted bitsEquiv
      portVariable bits_port s p
  · exact ColoringConnectedMacroSemantics.inverse_gray occurrence left right shape source
      ColoringCrossMacroCore.cover ColoringCrossMacroCore.coherent (component left right 0) accepted bitsEquiv s p
  · exact ColoringConnectedMacroSemantics.inverse_black occurrence left right shape source
      ColoringCrossMacroCore.cover ColoringCrossMacroCore.coherent (component left right 0) accepted bitsEquiv s p

def numericEquiv : Coloring ColoringCrossMacroCoordinates.graph ≃ State (Fin 4) accepted :=
  ColoringCrossMacroTyped.numericEquiv.colorings.symm.trans typedEquiv

theorem numeric_inverse_port (s : State (Fin 4) accepted) (p : Fin 4) (k : Fin 3) :
    (numericEquiv.symm s).val (boundaryIds p k)=portColor s (p,k) := by
  change (typedEquiv.symm s).val (number.symm (boundaryIds p k))=_
  rw [←boundary_number,Equiv.symm_apply_apply]
  exact typed_inverse_port s p k

end PlanarHom.ColoringCrossMacroSemantics
