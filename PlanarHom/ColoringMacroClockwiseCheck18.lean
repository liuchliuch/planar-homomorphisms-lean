import PlanarHom.ColoringMacroClockwiseCheck17
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_21 : ∀i : Fin 32,ClockwiseRow .cross ⟨672+i.val,by change 672+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_22 : ∀i : Fin 32,ClockwiseRow .cross ⟨704+i.val,by change 704+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_23 : ∀i : Fin 32,ClockwiseRow .cross ⟨736+i.val,by change 736+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_24 : ∀i : Fin 32,ClockwiseRow .cross ⟨768+i.val,by change 768+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
