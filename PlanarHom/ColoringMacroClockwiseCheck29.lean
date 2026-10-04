import PlanarHom.ColoringMacroClockwiseCheck28
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_fan_25 : ∀i : Fin 32,ClockwiseRow .fan ⟨800+i.val,by change 800+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_26 : ∀i : Fin 32,ClockwiseRow .fan ⟨832+i.val,by change 832+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_27 : ∀i : Fin 32,ClockwiseRow .fan ⟨864+i.val,by change 864+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_28 : ∀i : Fin 32,ClockwiseRow .fan ⟨896+i.val,by change 896+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
