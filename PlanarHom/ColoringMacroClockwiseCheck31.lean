import PlanarHom.ColoringMacroClockwiseCheck30
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem clockwise_test_0 : ∀i : Fin 32,ClockwiseRow .test ⟨0+i.val,by change 0+i.val<114; omega⟩ := by decide +kernel

theorem clockwise_test_1 : ∀i : Fin 32,ClockwiseRow .test ⟨32+i.val,by change 32+i.val<114; omega⟩ := by decide +kernel

theorem clockwise_test_2 : ∀i : Fin 32,ClockwiseRow .test ⟨64+i.val,by change 64+i.val<114; omega⟩ := by decide +kernel

theorem clockwise_test_3 : ∀i : Fin 18,ClockwiseRow .test ⟨96+i.val,by change 96+i.val<114; omega⟩ := by decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
