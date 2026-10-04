import PlanarHom.ColoringCanvasStraightDrawing
import PlanarHom.StraightDrawingGerms

noncomputable section
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph PositiveBlockProgram ParsimoniousNorOneInThree IntegerStraightDrawing
open MultiGraph.Kasteleyn PlanarityLRRealization

def shear : C(Plane,Plane) where
  toFun p := (p.1+p.2/1000000000000,p.2)
  continuous_toFun := by fun_prop

theorem shear_injective : Function.Injective shear := by
  intro a b h
  have hx:=congrArg Prod.fst h
  have hy:=congrArg Prod.snd h
  dsimp [shear] at hx hy
  exact Prod.ext (by linarith) hy

theorem shear_affine (a b : Plane) (t : ℝ) :
    shear (affine a b t)=affine (shear a) (shear b) t := by
  apply Prod.ext <;> dsimp [shear,affine] <;> ring

def shearedDrawingFrom (D : MacroGeometry.RawDrawings) (f : NumericFormula) : PlaneDrawing (graph f) :=
  mapDrawing (drawingFrom D f) shear shear_injective

theorem shearedDrawingFrom_straight (D : MacroGeometry.RawDrawings) (f : NumericFormula) :
    (shearedDrawingFrom D f).Straight := (drawingFrom_straight D f).map shear shear_injective shear_affine

def shearedPolygonalFrom (D : MacroGeometry.RawDrawings) (f : NumericFormula) : PolygonalDrawing (graph f) :=
  (shearedDrawingFrom_straight D f).polygonal

theorem shearedGermFrom (D : MacroGeometry.RawDrawings) (f : NumericFormula) (a : Dart (Edge f)) :
    StraightGerm ((shearedDrawingFrom D f).dartPath a)
      ((shearedDrawingFrom D f).point ((graph f).dartPair a).1)
      ((shearedDrawingFrom D f).endpointRay a) := (shearedDrawingFrom_straight D f).germ a

end PlanarHom.ColoringEmitter.Canvas
