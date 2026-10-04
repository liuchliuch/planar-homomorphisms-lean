import PlanarHom.ColoringMacroClockwiseCheck3
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireTop_16 : ∀i : Fin 18,ClockwiseRow .wireTop ⟨512+i.val,by change 512+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_0 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨0+i.val,by change 0+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_1 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨32+i.val,by change 32+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_2 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨64+i.val,by change 64+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
