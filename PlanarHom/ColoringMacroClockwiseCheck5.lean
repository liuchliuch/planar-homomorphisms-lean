import PlanarHom.ColoringMacroClockwiseCheck4
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireBottom_3 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨96+i.val,by change 96+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_4 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨128+i.val,by change 128+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_5 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨160+i.val,by change 160+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_6 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨192+i.val,by change 192+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
