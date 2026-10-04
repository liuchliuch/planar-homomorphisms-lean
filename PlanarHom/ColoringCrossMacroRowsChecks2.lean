import PlanarHom.ColoringCrossMacroRowsChecks1
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_8 : ∀i : Fin 64,VertexGood ⟨512+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_9 : ∀i : Fin 64,VertexGood ⟨576+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_10 : ∀i : Fin 64,VertexGood ⟨640+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_11 : ∀i : Fin 64,VertexGood ⟨704+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
