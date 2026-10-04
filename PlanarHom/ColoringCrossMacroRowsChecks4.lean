import PlanarHom.ColoringCrossMacroRowsChecks3
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_16 : ∀i : Fin 64,VertexGood ⟨1024+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_17 : ∀i : Fin 64,VertexGood ⟨1088+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_18 : ∀i : Fin 64,VertexGood ⟨1152+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_19 : ∀i : Fin 54,VertexGood ⟨1216+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
