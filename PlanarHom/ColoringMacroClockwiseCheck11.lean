import PlanarHom.ColoringMacroClockwiseCheck10
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireDown_10 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨320+i.val,by change 320+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_11 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨352+i.val,by change 352+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_12 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨384+i.val,by change 384+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireDown_13 : ∀i : Fin 32,ClockwiseRow .wireDown ⟨416+i.val,by change 416+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
