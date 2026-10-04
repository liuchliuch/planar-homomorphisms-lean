import PlanarHom.ColoringMacroClockwiseCheck22
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_fan_1 : ∀i : Fin 32,ClockwiseRow .fan ⟨32+i.val,by change 32+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_2 : ∀i : Fin 32,ClockwiseRow .fan ⟨64+i.val,by change 64+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_3 : ∀i : Fin 32,ClockwiseRow .fan ⟨96+i.val,by change 96+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_4 : ∀i : Fin 32,ClockwiseRow .fan ⟨128+i.val,by change 128+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
