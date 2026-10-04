import PlanarHom.ColoringMacroClockwiseCheck2
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireTop_12 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨384+i.val,by change 384+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_13 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨416+i.val,by change 416+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_14 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨448+i.val,by change 448+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_15 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨480+i.val,by change 480+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
