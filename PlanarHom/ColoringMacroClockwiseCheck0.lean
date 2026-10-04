import PlanarHom.ColoringMacroClockwisePredicates
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireTop_0 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨0+i.val,by change 0+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_1 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨32+i.val,by change 32+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_2 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨64+i.val,by change 64+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_3 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨96+i.val,by change 96+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
