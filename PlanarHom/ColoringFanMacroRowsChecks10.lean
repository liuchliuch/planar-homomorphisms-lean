import PlanarHom.ColoringFanMacroRowsChecks9
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_23 : ∀i : Fin 64,DartGood ⟨1472+i.val,by omega⟩ := by decide +kernel

theorem DartGood_24 : ∀i : Fin 64,DartGood ⟨1536+i.val,by omega⟩ := by decide +kernel

theorem DartGood_25 : ∀i : Fin 64,DartGood ⟨1600+i.val,by omega⟩ := by decide +kernel

theorem DartGood_26 : ∀i : Fin 64,DartGood ⟨1664+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
