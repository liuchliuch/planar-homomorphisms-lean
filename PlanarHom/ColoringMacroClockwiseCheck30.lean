import PlanarHom.ColoringMacroClockwiseCheck29
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_fan_29 : ∀i : Fin 32,ClockwiseRow .fan ⟨928+i.val,by change 928+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_30 : ∀i : Fin 32,ClockwiseRow .fan ⟨960+i.val,by change 960+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_31 : ∀i : Fin 32,ClockwiseRow .fan ⟨992+i.val,by change 992+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_32 : ∀i : Fin 30,ClockwiseRow .fan ⟨1024+i.val,by change 1024+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
