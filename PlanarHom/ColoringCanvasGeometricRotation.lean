import PlanarHom.ColoringCanvasDrawing
import PlanarHom.ColoringMacroClockwiseOrder
import PlanarHom.ColoringCanvasRotationOrder
import PlanarHom.ColoringEmitterComputedRows
import PlanarHom.ColoringCanvasNoIsolates
import PlanarHom.GeometricRowsTransport
import PlanarHom.RadialPottsAssemblyGeometricRows

/-! The source compiler's actual sheared polygonal drawing, its literal computed
clockwise rows and straight nonvertical dart germs. These are the exact graph
occurrences consumed by the numeric emitter and radial query construction. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree
open PlanarityLRRealization RadialPottsAssemblyGeometry

def geometricDrawing (f : NumericFormula) : PlaneDrawing (graph f) :=
  shearedDrawingFrom MacroGeometry.actualRawDrawings f

def geometricPolygonal (f : NumericFormula) : PolygonalDrawing (graph f) :=
  shearedPolygonalFrom MacroGeometry.actualRawDrawings f

def geometricRays (f : NumericFormula) : Dart (Edge f) → Plane := (geometricDrawing f).endpointRay

theorem geometric_straight (f : NumericFormula) : (geometricDrawing f).Straight :=
  shearedDrawingFrom_straight MacroGeometry.actualRawDrawings f

theorem geometric_germ (f : NumericFormula) (a : Dart (Edge f)) :
    StraightGerm ((geometricDrawing f).dartPath a) ((geometricDrawing f).point ((graph f).dartPair a).1)
      (geometricRays f a) := (geometric_straight f).germ a

theorem geometric_nonvertical (f : NumericFormula) (a : Dart (Edge f)) : (geometricRays f a).1≠0 :=
  sheared_endpointRay_nonvertical MacroGeometry.actualRawDrawings f a

theorem geometric_clockwise (f : NumericFormula) (v : Vertex f) :
    ((geometricRows f).row v).Pairwise (fun a b=>ClockwiseRayOrder (geometricRays f a) (geometricRays f b)) :=
  rowsFrom_clockwise MacroGeometry.actualRawDrawings f _
    (fun i w=>MacroGeometry.localRows_clockwise (canvasCell f i).shape w) v

def numericDrawing (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    PlaneDrawing ((compile f).toMultiGraph (compile_valid f)) :=
  (geometricDrawing f).transport (compile_incidenceEquiv f hf hne)

theorem numeric_straight (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    (numericDrawing f hf hne).Straight := (geometric_straight f).transport (compile_incidenceEquiv f hf hne)

def numericPolygonal (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    PolygonalDrawing ((compile f).toMultiGraph (compile_valid f)) := (numeric_straight f hf hne).polygonal

def numericRays (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    Dart (Fin (compile f).edges.length) → Plane := (numericDrawing f hf hne).endpointRay

theorem numeric_germ (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[])
    (a : Dart (Fin (compile f).edges.length)) :
    StraightGerm ((numericDrawing f hf hne).dartPath a)
      ((numericDrawing f hf hne).point (((compile f).toMultiGraph (compile_valid f)).dartPair a).1)
      (numericRays f hf hne a) := (numeric_straight f hf hne).germ a

theorem numeric_nonvertical (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[])
    (a : Dart (Fin (compile f).edges.length)) : (numericRays f hf hne a).1≠0 :=
  (geometricDrawing f).nonvertical_transport (compile_incidenceEquiv f hf hne) (geometric_nonvertical f) a

theorem numeric_clockwise (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[])
    (v : Fin (compile f).vertices) :
    ((computedGeometricRows f hf hne).row v).Pairwise (fun a b=>
      ClockwiseRayOrder (numericRays f hf hne a) (numericRays f hf hne b)) :=
  (geometricRows f).clockwise_transport (geometricDrawing f) (compile_incidenceEquiv f hf hne)
    (geometric_clockwise f) v

/-- Actual radial query graph planarity for every subdivision count, directly
from the emitted source's geometric rows. No computed LR drawing is used. -/
theorem numeric_radial_planar (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) (k : ℕ) :
    (RadialPotts.Assembly.graph (computedGeometricRows f hf hne).rotation k).Planar :=
  RadialPotts.Assembly.planar_of_clockwiseRows (numericPolygonal f hf hne) (numericRays f hf hne)
    (numeric_germ f hf hne) (computedGeometricRows f hf hne) (numeric_nonvertical f hf hne)
    (numeric_clockwise f hf hne) k

end PlanarHom.ColoringEmitter.Canvas
