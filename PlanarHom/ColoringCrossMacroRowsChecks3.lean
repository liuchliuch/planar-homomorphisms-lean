import PlanarHom.ColoringCrossMacroRowsChecks2
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_12 : ∀i : Fin 64,VertexGood ⟨768+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_13 : ∀i : Fin 64,VertexGood ⟨832+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_14 : ∀i : Fin 64,VertexGood ⟨896+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_15 : ∀i : Fin 64,VertexGood ⟨960+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
