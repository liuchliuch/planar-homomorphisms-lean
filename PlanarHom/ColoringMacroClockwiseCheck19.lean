import PlanarHom.ColoringMacroClockwiseCheck18
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_25 : ∀i : Fin 32,ClockwiseRow .cross ⟨800+i.val,by change 800+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_26 : ∀i : Fin 32,ClockwiseRow .cross ⟨832+i.val,by change 832+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_27 : ∀i : Fin 32,ClockwiseRow .cross ⟨864+i.val,by change 864+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_28 : ∀i : Fin 32,ClockwiseRow .cross ⟨896+i.val,by change 896+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
