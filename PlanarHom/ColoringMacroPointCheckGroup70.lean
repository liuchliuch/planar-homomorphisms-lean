import PlanarHom.ColoringMacroFastEdgeBounds
import PlanarHom.ColoringMacroPointCheckGroup69

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_fan_EdgeInterior_39 : ∀i : Fin 64,EdgeInterior .fan ⟨2496+i.val,by change 2496+i.val<2619; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_fan_EdgeInterior_40 : ∀i : Fin 59,EdgeInterior .fan ⟨2560+i.val,by change 2560+i.val<2619; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_test_PointBound_0 : ∀i : Fin 64,PointBound .test ⟨0+i.val,by change 0+i.val<114; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_test_PointBound_1 : ∀i : Fin 50,PointBound .test ⟨64+i.val,by change 64+i.val<114; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry
