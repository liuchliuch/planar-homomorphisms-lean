import PlanarHom.ColoringCrossMacroRowsChecks12
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_32 : ∀i : Fin 64,DartGood ⟨2048+i.val,by omega⟩ := by decide +kernel

theorem DartGood_33 : ∀i : Fin 64,DartGood ⟨2112+i.val,by omega⟩ := by decide +kernel

theorem DartGood_34 : ∀i : Fin 64,DartGood ⟨2176+i.val,by omega⟩ := by decide +kernel

theorem DartGood_35 : ∀i : Fin 64,DartGood ⟨2240+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
