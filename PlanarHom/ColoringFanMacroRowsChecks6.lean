import PlanarHom.ColoringFanMacroRowsChecks5
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_7 : ∀i : Fin 64,DartGood ⟨448+i.val,by omega⟩ := by decide +kernel

theorem DartGood_8 : ∀i : Fin 64,DartGood ⟨512+i.val,by omega⟩ := by decide +kernel

theorem DartGood_9 : ∀i : Fin 64,DartGood ⟨576+i.val,by omega⟩ := by decide +kernel

theorem DartGood_10 : ∀i : Fin 64,DartGood ⟨640+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
