import PlanarHom.ColoringMacroClockwiseCheck8
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireDown_2 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨64+i.val,by change 64+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_3 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨96+i.val,by change 96+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_4 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨128+i.val,by change 128+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_5 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨160+i.val,by change 160+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
