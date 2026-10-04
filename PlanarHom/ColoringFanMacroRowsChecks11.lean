import PlanarHom.ColoringFanMacroRowsChecks10
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_27 : ∀i : Fin 64,DartGood ⟨1728+i.val,by omega⟩ := by decide +kernel

theorem DartGood_28 : ∀i : Fin 64,DartGood ⟨1792+i.val,by omega⟩ := by decide +kernel

theorem DartGood_29 : ∀i : Fin 64,DartGood ⟨1856+i.val,by omega⟩ := by decide +kernel

theorem DartGood_30 : ∀i : Fin 64,DartGood ⟨1920+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
