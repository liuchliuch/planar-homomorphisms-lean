import PlanarHom.ColoringFanMacroRowsPredicates
noncomputable section
namespace PlanarHom.ColoringFanMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_0 : ∀i : Fin 64,VertexGood ⟨0+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_1 : ∀i : Fin 64,VertexGood ⟨64+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_2 : ∀i : Fin 64,VertexGood ⟨128+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_3 : ∀i : Fin 64,VertexGood ⟨192+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringFanMacroRows
