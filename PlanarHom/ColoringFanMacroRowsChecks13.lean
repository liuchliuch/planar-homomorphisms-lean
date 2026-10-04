import PlanarHom.ColoringFanMacroRowsChecks12
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_35 : ∀i : Fin 64,DartGood ⟨2240+i.val,by omega⟩ := by decide +kernel

theorem DartGood_36 : ∀i : Fin 64,DartGood ⟨2304+i.val,by omega⟩ := by decide +kernel

theorem DartGood_37 : ∀i : Fin 64,DartGood ⟨2368+i.val,by omega⟩ := by decide +kernel

theorem DartGood_38 : ∀i : Fin 64,DartGood ⟨2432+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
