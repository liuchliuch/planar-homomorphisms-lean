import PlanarHom.ColoringMacroClockwiseCheck12
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_1 : ∀i : Fin 32,ClockwiseRow .cross ⟨32+i.val,by change 32+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_2 : ∀i : Fin 32,ClockwiseRow .cross ⟨64+i.val,by change 64+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_3 : ∀i : Fin 32,ClockwiseRow .cross ⟨96+i.val,by change 96+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_4 : ∀i : Fin 32,ClockwiseRow .cross ⟨128+i.val,by change 128+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
