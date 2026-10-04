import PlanarHom.ColoringEmitterMacroRows
import PlanarHom.ColoringMacroIntegerRays

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram

def ClockwiseRow (s : CellShape) (v : LocalPatch.NumericVertex s) : Prop :=
  ((MacroRows.numericRows s).row v).Pairwise (fun a b=>IntegerClockwise (integerRay s a) (integerRay s b))
instance (s : CellShape) (v : LocalPatch.NumericVertex s) : Decidable (ClockwiseRow s v) :=
  inferInstanceAs (Decidable (List.Pairwise _ _))

end PlanarHom.ColoringEmitter.MacroGeometry
