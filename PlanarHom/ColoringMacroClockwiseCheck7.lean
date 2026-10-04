import PlanarHom.ColoringMacroClockwiseCheck6
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireBottom_11 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨352+i.val,by change 352+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_12 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨384+i.val,by change 384+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_13 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨416+i.val,by change 416+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireBottom_14 : ∀i : Fin 32,ClockwiseRow .wireBottom ⟨448+i.val,by change 448+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
