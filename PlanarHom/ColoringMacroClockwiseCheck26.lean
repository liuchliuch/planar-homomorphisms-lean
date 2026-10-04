import PlanarHom.ColoringMacroClockwiseCheck25
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_fan_13 : ∀i : Fin 32,ClockwiseRow .fan ⟨416+i.val,by change 416+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_14 : ∀i : Fin 32,ClockwiseRow .fan ⟨448+i.val,by change 448+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_15 : ∀i : Fin 32,ClockwiseRow .fan ⟨480+i.val,by change 480+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_16 : ∀i : Fin 32,ClockwiseRow .fan ⟨512+i.val,by change 512+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
