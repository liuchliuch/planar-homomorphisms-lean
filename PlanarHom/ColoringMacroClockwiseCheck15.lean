import PlanarHom.ColoringMacroClockwiseCheck14
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_cross_9 : ∀i : Fin 32,ClockwiseRow .cross ⟨288+i.val,by change 288+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_10 : ∀i : Fin 32,ClockwiseRow .cross ⟨320+i.val,by change 320+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_11 : ∀i : Fin 32,ClockwiseRow .cross ⟨352+i.val,by change 352+i.val<1270; omega⟩ := by decide +kernel

theorem clockwise_cross_12 : ∀i : Fin 32,ClockwiseRow .cross ⟨384+i.val,by change 384+i.val<1270; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
