import PlanarHom.ColoringCrossMacroRowsChecks16
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_48 : ∀i : Fin 64,DartGood ⟨3072+i.val,by omega⟩ := by decide +kernel

theorem DartGood_49 : ∀i : Fin 16,DartGood ⟨3136+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
