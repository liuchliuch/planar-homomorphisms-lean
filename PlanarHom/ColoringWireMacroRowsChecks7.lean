import PlanarHom.ColoringWireMacroRowsChecks6
noncomputable section
namespace PlanarHom.ColoringWireMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_19 : ∀i : Fin 64,DartGood ⟨1216+i.val,by omega⟩ := by decide +kernel

theorem DartGood_20 : ∀i : Fin 33,DartGood ⟨1280+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringWireMacroRows
