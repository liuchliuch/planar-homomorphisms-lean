import PlanarHom.ColoringMacroFastEdgeBounds
import PlanarHom.ColoringMacroPointCheckGroup28

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireDown_EdgeInterior_20 : ∀i : Fin 33,EdgeInterior .wireDown ⟨1280+i.val,by change 1280+i.val<1313; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_cross_PointBound_0 : ∀i : Fin 64,PointBound .cross ⟨0+i.val,by change 0+i.val<1270; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_cross_PointBound_1 : ∀i : Fin 64,PointBound .cross ⟨64+i.val,by change 64+i.val<1270; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_cross_PointBound_2 : ∀i : Fin 64,PointBound .cross ⟨128+i.val,by change 128+i.val<1270; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry
