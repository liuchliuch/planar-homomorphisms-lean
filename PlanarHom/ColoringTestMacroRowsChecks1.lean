import PlanarHom.ColoringTestMacroRowsChecks0
noncomputable section
namespace PlanarHom.ColoringTestMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_2 : ∀i : Fin 64,DartGood ⟨128+i.val,by omega⟩ := by decide +kernel

theorem DartGood_3 : ∀i : Fin 64,DartGood ⟨192+i.val,by omega⟩ := by decide +kernel

theorem DartGood_4 : ∀i : Fin 16,DartGood ⟨256+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringTestMacroRows
