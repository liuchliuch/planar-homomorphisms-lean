import PlanarHom.ColoringMacroPointData
import PlanarHom.ColoringWireMacroEmitterJoin
import PlanarHom.ColoringCrossMacroEmitterJoin
import PlanarHom.ColoringFanMacroEmitterJoin
import PlanarHom.ColoringTestMacroEmitterJoin

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fastSource (s : CellShape) (e : LocalPatch.Edge s) : LocalPatch.NumericVertex s :=
  match s with
  | .wireTop | .wireBottom | .wireDown => ColoringWireMacroCoordinates.graph.src (ColoringWireMacroEmitterJoin.edgeIndex e)
  | .cross => ColoringCrossMacroCoordinates.graph.src (ColoringCrossMacroEmitterJoin.edgeIndex e)
  | .fan => ColoringFanMacroCoordinates.graph.src (ColoringFanMacroEmitterJoin.edgeIndex e)
  | .test => ColoringTestMacroCoordinates.graph.src (ColoringTestMacroEmitterJoin.edgeIndex e)

def fastTarget (s : CellShape) (e : LocalPatch.Edge s) : LocalPatch.NumericVertex s :=
  match s with
  | .wireTop | .wireBottom | .wireDown => ColoringWireMacroCoordinates.graph.dst (ColoringWireMacroEmitterJoin.edgeIndex e)
  | .cross => ColoringCrossMacroCoordinates.graph.dst (ColoringCrossMacroEmitterJoin.edgeIndex e)
  | .fan => ColoringFanMacroCoordinates.graph.dst (ColoringFanMacroEmitterJoin.edgeIndex e)
  | .test => ColoringTestMacroCoordinates.graph.dst (ColoringTestMacroEmitterJoin.edgeIndex e)

theorem fastSource_eq (s : CellShape) (e : LocalPatch.Edge s) :
    fastSource s e=(LocalPatch.numericGraph s).src e := by
  cases s <;> apply Fin.ext
  all_goals first
    | exact (congrArg Prod.fst (ColoringWireMacroEmitterJoin.edgePair_eq e)).symm
    | exact (congrArg Prod.fst (ColoringCrossMacroEmitterJoin.edgePair_eq e)).symm
    | exact (congrArg Prod.fst (ColoringFanMacroEmitterJoin.edgePair_eq e)).symm
    | exact (congrArg Prod.fst (ColoringTestMacroEmitterJoin.edgePair_eq e)).symm

theorem fastTarget_eq (s : CellShape) (e : LocalPatch.Edge s) :
    fastTarget s e=(LocalPatch.numericGraph s).dst e := by
  cases s <;> apply Fin.ext
  all_goals first
    | exact (congrArg Prod.snd (ColoringWireMacroEmitterJoin.edgePair_eq e)).symm
    | exact (congrArg Prod.snd (ColoringCrossMacroEmitterJoin.edgePair_eq e)).symm
    | exact (congrArg Prod.snd (ColoringFanMacroEmitterJoin.edgePair_eq e)).symm
    | exact (congrArg Prod.snd (ColoringTestMacroEmitterJoin.edgePair_eq e)).symm

def FastEdgeInterior (s : CellShape) (e : LocalPatch.Edge s) : Prop :=
  let a:=integerPoint s (fastSource s e)
  let b:=integerPoint s (fastTarget s e)
  (0<a.1 ∨ 0<b.1) ∧ (a.1<width s ∨ b.1<width s)
instance (s : CellShape) (e : LocalPatch.Edge s) : Decidable (FastEdgeInterior s e) := inferInstanceAs (Decidable (_ ∧ _))

theorem edgeInterior_eq_fast (s : CellShape) (e : LocalPatch.Edge s) :
    EdgeInterior s e ↔ FastEdgeInterior s e := by
  simp only [FastEdgeInterior,fastSource_eq,fastTarget_eq]
  rfl

end PlanarHom.ColoringEmitter.MacroGeometry
