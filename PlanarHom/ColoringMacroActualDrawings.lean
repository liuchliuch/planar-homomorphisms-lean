import PlanarHom.ColoringWireMacroDrawing
import PlanarHom.ColoringCrossMacroDrawing
import PlanarHom.ColoringFanMacroDrawing
import PlanarHom.ColoringTestMacroDrawing
import PlanarHom.ColoringMacroPlacedDrawing
import PlanarHom.StraightDrawingTransport

/-! Closing the placed-macro drawing interface with the four independently
kernel-checked literal integer drawings. -/
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing

def actualBaseDrawing (s : CellShape) : PlaneDrawing (LocalPatch.numericGraph s) :=
  match s with
  | .wireTop | .wireBottom | .wireDown =>
    ColoringWireMacroCoordinates.drawing.transport ColoringWireMacroEmitterJoin.numericEquiv.symm
  | .cross => ColoringCrossMacroCoordinates.drawing.transport ColoringCrossMacroEmitterJoin.numericEquiv.symm
  | .fan => ColoringFanMacroCoordinates.drawing.transport ColoringFanMacroEmitterJoin.numericEquiv.symm
  | .test => ColoringTestMacroCoordinates.drawing.transport ColoringTestMacroEmitterJoin.numericEquiv.symm

def actualRawDrawings : RawDrawings where
  drawing := actualBaseDrawing
  point s v := by cases s <;> rfl
  straight s := by
    cases s
    all_goals apply PlaneDrawing.Straight.transport
    all_goals intro e t; rfl

end PlanarHom.ColoringEmitter.MacroGeometry
