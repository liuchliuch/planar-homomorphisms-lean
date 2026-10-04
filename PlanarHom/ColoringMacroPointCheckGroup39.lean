import PlanarHom.ColoringMacroFastEdgeBounds
import PlanarHom.ColoringMacroPointCheckGroup38

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_cross_InteriorOrPort_19 : ∀i : Fin 54,InteriorOrPort .cross ⟨1216+i.val,by change 1216+i.val<1270; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_cross_EdgeInterior_0 : ∀i : Fin 64,EdgeInterior .cross ⟨0+i.val,by change 0+i.val<3152; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_cross_EdgeInterior_1 : ∀i : Fin 64,EdgeInterior .cross ⟨64+i.val,by change 64+i.val<3152; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_cross_EdgeInterior_2 : ∀i : Fin 64,EdgeInterior .cross ⟨128+i.val,by change 128+i.val<3152; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry
