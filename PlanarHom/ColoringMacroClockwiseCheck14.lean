import PlanarHom.ColoringMacroClockwiseCheck13
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_5 : ∀i : Fin 32,ClockwiseRow .cross ⟨160+i.val,by change 160+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_6 : ∀i : Fin 32,ClockwiseRow .cross ⟨192+i.val,by change 192+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_7 : ∀i : Fin 32,ClockwiseRow .cross ⟨224+i.val,by change 224+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_8 : ∀i : Fin 32,ClockwiseRow .cross ⟨256+i.val,by change 256+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
