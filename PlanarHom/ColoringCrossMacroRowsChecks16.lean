import PlanarHom.ColoringCrossMacroRowsChecks15
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_44 : ∀i : Fin 64,DartGood ⟨2816+i.val,by omega⟩ := by decide +kernel

theorem DartGood_45 : ∀i : Fin 64,DartGood ⟨2880+i.val,by omega⟩ := by decide +kernel

theorem DartGood_46 : ∀i : Fin 64,DartGood ⟨2944+i.val,by omega⟩ := by decide +kernel

theorem DartGood_47 : ∀i : Fin 64,DartGood ⟨3008+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
