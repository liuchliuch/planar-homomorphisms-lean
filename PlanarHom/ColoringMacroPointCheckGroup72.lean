import PlanarHom.ColoringMacroFastEdgeBounds
import PlanarHom.ColoringMacroPointCheckGroup71

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_test_EdgeInterior_2 : ∀i : Fin 64,EdgeInterior .test ⟨128+i.val,by change 128+i.val<272; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_test_EdgeInterior_3 : ∀i : Fin 64,EdgeInterior .test ⟨192+i.val,by change 192+i.val<272; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_test_EdgeInterior_4 : ∀i : Fin 16,EdgeInterior .test ⟨256+i.val,by change 256+i.val<272; omega⟩ := by simp_rw [edgeInterior_eq_fast]; decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry
