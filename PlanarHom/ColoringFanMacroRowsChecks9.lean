import PlanarHom.ColoringFanMacroRowsChecks8
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_19 : ∀i : Fin 64,DartGood ⟨1216+i.val,by omega⟩ := by decide +kernel

theorem DartGood_20 : ∀i : Fin 64,DartGood ⟨1280+i.val,by omega⟩ := by decide +kernel

theorem DartGood_21 : ∀i : Fin 64,DartGood ⟨1344+i.val,by omega⟩ := by decide +kernel

theorem DartGood_22 : ∀i : Fin 64,DartGood ⟨1408+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
