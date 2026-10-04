import PlanarHom.PalettedAssemblyComponents
import PlanarHom.ColoringCanvasSourceSolutions
import PlanarHom.ColoringEmitterMacroSemantics
import PlanarHom.ColoringEmitterCanvas
import PlanarHom.ColoringCanvasPortCoverage

/-! NEW exact source-solution count of the actual canonical coloring canvas.
One palette is retained for every actual graph component; no macro multiplicity,
free internal color, or free routed Boolean auxiliary remains. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringCanvasBoolean
open MultiGraph ThreeColorPaletteCounting ParsimoniousNorOneInThree PositiveBlockProgram
open PalettedColoringPatches ColoringEmitter
variable (f:NumericFormula) (hf:NumericValid f) (hne:f.2≠[])

 def canvasPatches (i:CanvasIndex f) := MacroSemantics.patch (canvasCell f i).shape

 def canvasBitsEquiv : PalettedColoringPatches.GlobalBits (canvasPatches f) (boundaryPort f) ≃ BoundarySolutions f :=
  Equiv.refl _

include hf hne in
 theorem canvas_count :
    ProperColoringPottsReduction.properColoringCount (Canvas.graph f) 3=
      6^((Canvas.graph f).componentCount Finset.univ)*Nat.card (NorExactOne.Solutions f) := by
  have hh:=PalettedColoringPatches.coloring_count_components (canvasPatches f) (boundaryPort f)
    (canvas_boundary_port_coverage f hf hne)
    (fun i=>⟨MacroSemantics.witness (canvasCell f i).shape⟩)
  have hb:Nat.card (PalettedColoringPatches.GlobalBits (canvasPatches f) (boundaryPort f))=
      Nat.card (NorExactOne.Solutions f) :=
    (Nat.card_congr (canvasBitsEquiv f)).trans (boundary_count f hf)
  rw [hb] at hh
  exact hh

 def canvasColoringEquiv : Coloring (Canvas.graph f) ≃
    (PalettedColoringPatches.SignalComponent (boundaryPort f)→Palette) × NorExactOne.Solutions f :=
  (PalettedColoringPatches.coloringPaletteEquiv (canvasPatches f) (boundaryPort f)
    (canvas_boundary_port_coverage f hf hne)).trans
      (Equiv.prodCongr (Equiv.refl _) ((canvasBitsEquiv f).trans (sourceBoundaryEquiv f hf).symm))

end PlanarHom.ColoringCanvasBoolean
