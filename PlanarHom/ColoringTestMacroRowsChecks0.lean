import PlanarHom.ColoringTestMacroRowsPredicates
noncomputable section
namespace PlanarHom.ColoringTestMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_0 : ∀i : Fin 64,VertexGood ⟨0+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_1 : ∀i : Fin 50,VertexGood ⟨64+i.val,by omega⟩ := by decide +kernel

theorem DartGood_0 : ∀i : Fin 64,DartGood ⟨0+i.val,by omega⟩ := by decide +kernel

theorem DartGood_1 : ∀i : Fin 64,DartGood ⟨64+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringTestMacroRows
