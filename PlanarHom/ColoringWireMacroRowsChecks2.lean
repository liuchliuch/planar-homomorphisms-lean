import PlanarHom.ColoringWireMacroRowsChecks1
noncomputable section
namespace PlanarHom.ColoringWireMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_8 : ∀i : Fin 18,VertexGood ⟨512+i.val,by omega⟩ := by decide +kernel

theorem DartGood_0 : ∀i : Fin 64,DartGood ⟨0+i.val,by omega⟩ := by decide +kernel

theorem DartGood_1 : ∀i : Fin 64,DartGood ⟨64+i.val,by omega⟩ := by decide +kernel

theorem DartGood_2 : ∀i : Fin 64,DartGood ⟨128+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringWireMacroRows
