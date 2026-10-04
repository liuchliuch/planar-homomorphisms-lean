import PlanarHom.ColoringMacroClockwiseCheck16
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_17 : ∀i : Fin 32,ClockwiseRow .cross ⟨544+i.val,by change 544+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_18 : ∀i : Fin 32,ClockwiseRow .cross ⟨576+i.val,by change 576+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_19 : ∀i : Fin 32,ClockwiseRow .cross ⟨608+i.val,by change 608+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_20 : ∀i : Fin 32,ClockwiseRow .cross ⟨640+i.val,by change 640+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
