import PlanarHom.ColoringCanvasDrawingAssembly
import PlanarHom.StraightDrawingTransport

noncomputable section
namespace PlanarHom.ColoringEmitter
open MultiGraph PositiveBlockProgram IntegerStraightDrawing

namespace MacroGeometry

theorem normalizedDrawing_straight (D : RawDrawings) (s : CellShape) :
    (normalizedDrawing D s).Straight :=
  PlaneDrawing.Straight.map (D.straight s) (normalize s) (normalize_injective s) (normalize_affine s)

theorem patchDrawing_straight (D : RawDrawings) (s : CellShape) : (patchDrawing D s).Straight :=
  (normalizedDrawing_straight D s).transport (MacroSemantics.partsEquiv s).symm

theorem translate_affine (offset a b : Plane) (t : ℝ) :
    translatePlane offset (affine a b t)=affine (translatePlane offset a) (translatePlane offset b) t := by
  apply Prod.ext <;> dsimp [translatePlane,affine] <;> ring

theorem placedDrawing_straight (D : RawDrawings) (c : Cell) : (placedDrawing D c).Straight :=
  (patchDrawing_straight D c.shape).map (translatePlane _) (translatePlane_injective _) (translate_affine _)

end MacroGeometry
namespace Canvas
open ParsimoniousNorOneInThree

theorem drawingFrom_straight (D : MacroGeometry.RawDrawings) (f : NumericFormula) :
    (drawingFrom D f).Straight := by
  rintro ⟨i,e⟩ t
  change (MacroGeometry.placedDrawing D (canvasCell f i)).curve e t=
    affine
      (PortPatchAssembly.point (patch f) (fun i=>MacroGeometry.placedDrawing D (canvasCell f i))
        (point f) (PortPatchAssembly.placeVertex (port f) i ((patch f i).src e)))
      (PortPatchAssembly.point (patch f) (fun i=>MacroGeometry.placedDrawing D (canvasCell f i))
        (point f) (PortPatchAssembly.placeVertex (port f) i ((patch f i).dst e))) t
  rw [PortPatchAssembly.point_place,PortPatchAssembly.point_place]
  · exact MacroGeometry.placedDrawing_straight D (canvasCell f i) e t
  all_goals intro i p; exact MacroGeometry.placed_port D (canvasCell f i) p

def polygonalFrom (D : MacroGeometry.RawDrawings) (f : NumericFormula) : PolygonalDrawing (graph f) :=
  (drawingFrom_straight D f).polygonal

end Canvas
end PlanarHom.ColoringEmitter
