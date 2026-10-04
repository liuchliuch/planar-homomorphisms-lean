import PlanarHom.ColoringMacroClockwiseCheck7
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireBottom_15 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨480+i.val,by change 480+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_16 : ∀i : Fin 18,ClockwiseRow .wireBottom ⟨512+i.val,by change 512+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_0 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨0+i.val,by change 0+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_1 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨32+i.val,by change 32+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
