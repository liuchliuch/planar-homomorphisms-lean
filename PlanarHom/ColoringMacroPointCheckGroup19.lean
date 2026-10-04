import PlanarHom.ColoringMacroFastEdgeBounds
import PlanarHom.ColoringMacroPointCheckGroup18

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireBottom_EdgeInterior_19 : ∀i : Fin 64,EdgeInterior .wireBottom ⟨1216+i.val,by change 1216+i.val<1313; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireBottom_EdgeInterior_20 : ∀i : Fin 33,EdgeInterior .wireBottom ⟨1280+i.val,by change 1280+i.val<1313; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireDown_PointBound_0 : ∀i : Fin 64,PointBound .wireDown ⟨0+i.val,by change 0+i.val<530; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireDown_PointBound_1 : ∀i : Fin 64,PointBound .wireDown ⟨64+i.val,by change 64+i.val<530; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry
