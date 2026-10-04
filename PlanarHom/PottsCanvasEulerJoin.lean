import PlanarHom.PottsCanvasSourceReduction
import PlanarHom.PottsParallelSourceCompatibility
import PlanarHom.ColoringCanvasGeometricRotation
import PlanarHom.ColoringEmitterNoIsolates
import PlanarHom.ColoringEmitterRowsRealizes

/-! NEW final join, reducing the complete all-q hardness and both main source
statements to one concrete finite Euler identity. Every other source geometric,
row, counting, algorithmic and field-code obligation is discharged. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.PottsCanvasEulerJoin
open Complexity ParsimoniousNorOneInThree MultiGraph MultiGraph.Kasteleyn
open PlanarityLRRealization FinitePermutationCycles PottsSourceCoefficientQueries
open PottsCanvasSourceReduction ColoringEmitter

def SourceCanvasEuler : Prop :=
  ∀f : NumericFormula,∀hf : NumericValid f,∀hne : f.2≠[],
    (compile f).vertices+count ((Canvas.computedGeometricRows f hf hne).rotation *
      reversePerm (Fin (compile f).edges.length))=
    (compile f).edges.length+2*((compile f).toMultiGraph (compile_valid f)).componentCount Finset.univ

theorem compatible_of_euler (hEuler : SourceCanvasEuler) : SourceCanvasCompatible := by
  intro f hf hne t ht
  let base : CompatibleRows (compile f) (compile_valid f) (ColoringEmitterRows.compileRows f) := {
    typed:=Canvas.computedGeometricRows f hf hne
    realizes:=Canvas.compileRows_realizes f hf hne
    incident:=compile_dart_host_surjective f hf
    euler:=hEuler f hf hne
    drawing:=Canvas.numericPolygonal f hf hne
    rays:=Canvas.numericRays f hf hne
    germ:=Canvas.numeric_germ f hf hne
    nonvertical:=Canvas.numeric_nonvertical f hf hne
    clockwise:=Canvas.numeric_clockwise f hf hne }
  exact parallel_compatible (compile f) (compile_valid f) (ColoringEmitterRows.compileRows f) base t ht

theorem positivePottsFoundation_of_euler (hEuler : SourceCanvasEuler) :
    AlgebraicProductInterpolation.RealLanguage.PositivePottsFoundation :=
  positivePottsFoundation_of_canvas (compatible_of_euler hEuler)

end PlanarHom.PottsCanvasEulerJoin
