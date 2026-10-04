import PlanarHom.ColoringMacroClockwiseCheck20
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_33 : ∀i : Fin 32,ClockwiseRow .cross ⟨1056+i.val,by change 1056+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_34 : ∀i : Fin 32,ClockwiseRow .cross ⟨1088+i.val,by change 1088+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_35 : ∀i : Fin 32,ClockwiseRow .cross ⟨1120+i.val,by change 1120+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_36 : ∀i : Fin 32,ClockwiseRow .cross ⟨1152+i.val,by change 1152+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
