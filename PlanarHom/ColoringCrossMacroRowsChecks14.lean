import PlanarHom.ColoringCrossMacroRowsChecks13
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_36 : ∀i : Fin 64,DartGood ⟨2304+i.val,by omega⟩ := by decide +kernel

theorem DartGood_37 : ∀i : Fin 64,DartGood ⟨2368+i.val,by omega⟩ := by decide +kernel

theorem DartGood_38 : ∀i : Fin 64,DartGood ⟨2432+i.val,by omega⟩ := by decide +kernel

theorem DartGood_39 : ∀i : Fin 64,DartGood ⟨2496+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
