import PlanarHom.ColoringMacroClockwiseCheck0
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireTop_4 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨128+i.val,by change 128+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_5 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨160+i.val,by change 160+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_6 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨192+i.val,by change 192+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_7 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨224+i.val,by change 224+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
