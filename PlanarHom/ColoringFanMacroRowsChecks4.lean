import PlanarHom.ColoringFanMacroRowsChecks3
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_16 : ∀i : Fin 30,VertexGood ⟨1024+i.val,by omega⟩ := by decide +kernel

theorem DartGood_0 : ∀i : Fin 64,DartGood ⟨0+i.val,by omega⟩ := by decide +kernel

theorem DartGood_1 : ∀i : Fin 64,DartGood ⟨64+i.val,by omega⟩ := by decide +kernel

theorem DartGood_2 : ∀i : Fin 64,DartGood ⟨128+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
