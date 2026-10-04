import PlanarHom.ColoringCrossMacroRowsChecks5
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_4 : ∀i : Fin 64,DartGood ⟨256+i.val,by omega⟩ := by decide +kernel

theorem DartGood_5 : ∀i : Fin 64,DartGood ⟨320+i.val,by omega⟩ := by decide +kernel

theorem DartGood_6 : ∀i : Fin 64,DartGood ⟨384+i.val,by omega⟩ := by decide +kernel

theorem DartGood_7 : ∀i : Fin 64,DartGood ⟨448+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
