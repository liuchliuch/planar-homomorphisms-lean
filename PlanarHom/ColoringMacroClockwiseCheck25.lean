import PlanarHom.ColoringMacroClockwiseCheck24
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_fan_9 : ∀i : Fin 32,ClockwiseRow .fan ⟨288+i.val,by change 288+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_10 : ∀i : Fin 32,ClockwiseRow .fan ⟨320+i.val,by change 320+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_11 : ∀i : Fin 32,ClockwiseRow .fan ⟨352+i.val,by change 352+i.val<1054; omega⟩ := by decide +kernel

theorem clockwise_fan_12 : ∀i : Fin 32,ClockwiseRow .fan ⟨384+i.val,by change 384+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
