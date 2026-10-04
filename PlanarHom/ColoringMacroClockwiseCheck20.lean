import PlanarHom.ColoringMacroClockwiseCheck19
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_29 : ∀i : Fin 32,ClockwiseRow .cross ⟨928+i.val,by change 928+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_30 : ∀i : Fin 32,ClockwiseRow .cross ⟨960+i.val,by change 960+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_31 : ∀i : Fin 32,ClockwiseRow .cross ⟨992+i.val,by change 992+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_32 : ∀i : Fin 32,ClockwiseRow .cross ⟨1024+i.val,by change 1024+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
