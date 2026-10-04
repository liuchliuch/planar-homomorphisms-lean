import PlanarHom.ColoringMacroClockwiseCheck9
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireDown_6 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨192+i.val,by change 192+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_7 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨224+i.val,by change 224+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_8 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨256+i.val,by change 256+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_9 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨288+i.val,by change 288+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
