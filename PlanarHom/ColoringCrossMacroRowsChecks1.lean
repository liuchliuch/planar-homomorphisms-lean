import PlanarHom.ColoringCrossMacroRowsChecks0
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem VertexGood_4 : ∀i : Fin 64,VertexGood ⟨256+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_5 : ∀i : Fin 64,VertexGood ⟨320+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_6 : ∀i : Fin 64,VertexGood ⟨384+i.val,by omega⟩ := by decide +kernel

theorem VertexGood_7 : ∀i : Fin 64,VertexGood ⟨448+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
