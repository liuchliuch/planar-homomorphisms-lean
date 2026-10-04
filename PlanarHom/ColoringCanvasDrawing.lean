import PlanarHom.ColoringCanvasDrawingAssembly
import PlanarHom.ColoringMacroActualDrawings

noncomputable section
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph ParsimoniousNorOneInThree

/-- Actual ordinary plane drawing of every literal finite coloring canvas.
Every macro, endpoint, repeated edge occurrence, and isolated initial signal is
present; the numeric compiler's separate empty-source branch remains empty. -/
def drawing (f : NumericFormula) : PlaneDrawing (graph f) :=
  drawingFrom MacroGeometry.actualRawDrawings f

theorem planar (f : NumericFormula) : (graph f).Planar := ⟨drawing f⟩

end PlanarHom.ColoringEmitter.Canvas
