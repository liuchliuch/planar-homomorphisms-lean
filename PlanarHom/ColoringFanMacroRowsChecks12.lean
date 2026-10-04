import PlanarHom.ColoringFanMacroRowsChecks11
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_31 : ∀i : Fin 64,DartGood ⟨1984+i.val,by omega⟩ := by decide +kernel

theorem DartGood_32 : ∀i : Fin 64,DartGood ⟨2048+i.val,by omega⟩ := by decide +kernel

theorem DartGood_33 : ∀i : Fin 64,DartGood ⟨2112+i.val,by omega⟩ := by decide +kernel

theorem DartGood_34 : ∀i : Fin 64,DartGood ⟨2176+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
