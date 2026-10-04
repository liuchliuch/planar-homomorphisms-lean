import PlanarHom.ColoringMacroFastEdgeBounds
import PlanarHom.ColoringMacroPointCheckGroup23

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireDown_EdgeInterior_0 : ∀i : Fin 64,EdgeInterior .wireDown ⟨0+i.val,by change 0+i.val<1313; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireDown_EdgeInterior_1 : ∀i : Fin 64,EdgeInterior .wireDown ⟨64+i.val,by change 64+i.val<1313; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireDown_EdgeInterior_2 : ∀i : Fin 64,EdgeInterior .wireDown ⟨128+i.val,by change 128+i.val<1313; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireDown_EdgeInterior_3 : ∀i : Fin 64,EdgeInterior .wireDown ⟨192+i.val,by change 192+i.val<1313; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry
