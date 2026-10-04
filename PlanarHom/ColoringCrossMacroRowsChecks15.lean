import PlanarHom.ColoringCrossMacroRowsChecks14
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_40 : ∀i : Fin 64,DartGood ⟨2560+i.val,by omega⟩ := by decide +kernel

theorem DartGood_41 : ∀i : Fin 64,DartGood ⟨2624+i.val,by omega⟩ := by decide +kernel

theorem DartGood_42 : ∀i : Fin 64,DartGood ⟨2688+i.val,by omega⟩ := by decide +kernel

theorem DartGood_43 : ∀i : Fin 64,DartGood ⟨2752+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
