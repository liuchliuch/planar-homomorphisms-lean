import PlanarHom.ColoringMacroClockwiseCheck11
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireDown_14 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨448+i.val,by change 448+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_15 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨480+i.val,by change 480+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_16 : ∀i : Fin 18,ClockwiseRow .wireDown ⟨512+i.val,by change 512+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_cross_0 : ∀i : Fin 32,ClockwiseRow .cross ⟨0+i.val,by change 0+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
