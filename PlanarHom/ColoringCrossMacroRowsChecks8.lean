import PlanarHom.ColoringCrossMacroRowsChecks7
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_12 : ∀i : Fin 64,DartGood ⟨768+i.val,by omega⟩ := by decide +kernel

theorem DartGood_13 : ∀i : Fin 64,DartGood ⟨832+i.val,by omega⟩ := by decide +kernel

theorem DartGood_14 : ∀i : Fin 64,DartGood ⟨896+i.val,by omega⟩ := by decide +kernel

theorem DartGood_15 : ∀i : Fin 64,DartGood ⟨960+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
