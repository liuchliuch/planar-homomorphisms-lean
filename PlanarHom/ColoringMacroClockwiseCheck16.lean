import PlanarHom.ColoringMacroClockwiseCheck15
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_13 : ∀i : Fin 32,ClockwiseRow .cross ⟨416+i.val,by change 416+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_14 : ∀i : Fin 32,ClockwiseRow .cross ⟨448+i.val,by change 448+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_15 : ∀i : Fin 32,ClockwiseRow .cross ⟨480+i.val,by change 480+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_16 : ∀i : Fin 32,ClockwiseRow .cross ⟨512+i.val,by change 512+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
