import PlanarHom.ColoringFanMacroRowsChecks13
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_39 : ∀i : Fin 64,DartGood ⟨2496+i.val,by omega⟩ := by decide +kernel

theorem DartGood_40 : ∀i : Fin 59,DartGood ⟨2560+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
