import PlanarHom.ColoringCrossMacroRowsChecks4
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_0 : ∀i : Fin 64,DartGood ⟨0+i.val,by omega⟩ := by decide +kernel

theorem DartGood_1 : ∀i : Fin 64,DartGood ⟨64+i.val,by omega⟩ := by decide +kernel

theorem DartGood_2 : ∀i : Fin 64,DartGood ⟨128+i.val,by omega⟩ := by decide +kernel

theorem DartGood_3 : ∀i : Fin 64,DartGood ⟨192+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
