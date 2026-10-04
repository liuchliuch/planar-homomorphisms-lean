import PlanarHom.ColoringMacroPlacedDrawing

noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph PositiveBlockProgram ParsimoniousNorOneInThree

def point (f : NumericFormula) (b : BoundaryTriple f) : Plane := colorBoundaryPoint b.1.val b.2

theorem point_injective (f : NumericFormula) : Function.Injective (point f) := by
  intro p q h
  have he : (p.1.val,p.2)=(q.1.val,q.2) := @colorBoundaryPoint_injective (p.1.val,p.2) (q.1.val,q.2) h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun x : (ℕ×ℕ)×Fin 3=>x.1) he
  · exact congrArg (fun x : (ℕ×ℕ)×Fin 3=>x.2) he

def drawingFrom (D : MacroGeometry.RawDrawings) (f : NumericFormula) : PlaneDrawing (graph f) := by
  apply PortPatchAssembly.drawing (patch f)
    (fun i=>MacroGeometry.placedDrawing D (canvasCell f i))
    (fun i=>(canvasCell f i).colorBand) (point f) (port f)
  · exact canvas_colorBands_disjoint f
  · exact point_injective f
  · intro i b
    exact colorBoundaryPoint_outside (canvasCell f i) b.1.val b.2
  · intro i v
    exact MacroGeometry.placed_private D (canvasCell f i) v
  · intro i e t ht
    exact MacroGeometry.placed_curve D (canvasCell f i) e t ht
  · intro i p
    exact MacroGeometry.placed_port D (canvasCell f i) p

end PlanarHom.ColoringEmitter.Canvas
