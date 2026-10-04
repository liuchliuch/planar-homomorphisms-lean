import PlanarHom.ColoringMacroPointCheckGroup1

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireTop_PointBound_8 : ∀i : Fin 18,PointBound .wireTop ⟨512+i.val,by change 512+i.val<530; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireTop_InteriorOrPort_0 : ∀i : Fin 64,InteriorOrPort .wireTop ⟨0+i.val,by change 0+i.val<530; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireTop_InteriorOrPort_1 : ∀i : Fin 64,InteriorOrPort .wireTop ⟨64+i.val,by change 64+i.val<530; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem check_wireTop_InteriorOrPort_2 : ∀i : Fin 64,InteriorOrPort .wireTop ⟨128+i.val,by change 128+i.val<530; omega⟩ := by decide +kernel
end PlanarHom.ColoringEmitter.MacroGeometry
