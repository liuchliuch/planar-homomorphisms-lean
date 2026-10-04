import PlanarHom.ColoringMacroClockwiseCheck1
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_wireTop_8 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨256+i.val,by change 256+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_9 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨288+i.val,by change 288+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_10 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨320+i.val,by change 320+i.val<530; omega⟩ := by decide +kernel

theorem clockwise_wireTop_11 : ∀i : Fin 32,ClockwiseRow .wireTop ⟨352+i.val,by change 352+i.val<530; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
