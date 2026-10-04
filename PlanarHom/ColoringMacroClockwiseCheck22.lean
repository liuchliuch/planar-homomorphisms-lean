import PlanarHom.ColoringMacroClockwiseCheck21
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_37 : ∀i : Fin 32,ClockwiseRow .cross ⟨1184+i.val,by change 1184+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_38 : ∀i : Fin 32,ClockwiseRow .cross ⟨1216+i.val,by change 1216+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_39 : ∀i : Fin 22,ClockwiseRow .cross ⟨1248+i.val,by change 1248+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_fan_0 : ∀i : Fin 32,ClockwiseRow .fan ⟨0+i.val,by change 0+i.val<1054; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
