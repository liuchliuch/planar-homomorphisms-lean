import PlanarHom.ColoringMacroClockwiseCheck23
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_fan_5 : ∀i : Fin 32,ClockwiseRow .fan ⟨160+i.val,by change 160+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_6 : ∀i : Fin 32,ClockwiseRow .fan ⟨192+i.val,by change 192+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_7 : ∀i : Fin 32,ClockwiseRow .fan ⟨224+i.val,by change 224+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_8 : ∀i : Fin 32,ClockwiseRow .fan ⟨256+i.val,by change 256+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
