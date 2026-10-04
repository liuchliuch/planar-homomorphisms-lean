import PlanarHom.ColoringMacroClockwiseCheck27
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_fan_21 : ∀i : Fin 32,ClockwiseRow .fan ⟨672+i.val,by change 672+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_22 : ∀i : Fin 32,ClockwiseRow .fan ⟨704+i.val,by change 704+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_23 : ∀i : Fin 32,ClockwiseRow .fan ⟨736+i.val,by change 736+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_24 : ∀i : Fin 32,ClockwiseRow .fan ⟨768+i.val,by change 768+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
