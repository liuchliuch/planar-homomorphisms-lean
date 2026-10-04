import PlanarHom.ColoringMacroClockwiseCheck5
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireBottom_7 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨224+i.val,by change 224+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_8 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨256+i.val,by change 256+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_9 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨288+i.val,by change 288+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_10 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨320+i.val,by change 320+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
