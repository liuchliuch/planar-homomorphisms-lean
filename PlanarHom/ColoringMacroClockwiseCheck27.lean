import PlanarHom.ColoringMacroClockwiseCheck26
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_fan_17 : ∀i : Fin 32,ClockwiseRow .fan ⟨544+i.val,by change 544+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_18 : ∀i : Fin 32,ClockwiseRow .fan ⟨576+i.val,by change 576+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_19 : ∀i : Fin 32,ClockwiseRow .fan ⟨608+i.val,by change 608+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_20 : ∀i : Fin 32,ClockwiseRow .fan ⟨640+i.val,by change 640+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
