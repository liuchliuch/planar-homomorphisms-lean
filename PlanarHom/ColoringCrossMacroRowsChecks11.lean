import PlanarHom.ColoringCrossMacroRowsChecks10
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_24 : ∀i : Fin 64,DartGood ⟨1536+i.val,by omega⟩ := by decide +kernel

theorem DartGood_25 : ∀i : Fin 64,DartGood ⟨1600+i.val,by omega⟩ := by decide +kernel

theorem DartGood_26 : ∀i : Fin 64,DartGood ⟨1664+i.val,by omega⟩ := by decide +kernel

theorem DartGood_27 : ∀i : Fin 64,DartGood ⟨1728+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
