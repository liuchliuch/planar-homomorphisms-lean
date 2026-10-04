import PlanarHom.ColoringCrossMacroRowsChecks8
noncomputable section
namespace PlanarHom.ColoringCrossMacroRows
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem DartGood_16 : ∀i : Fin 64,DartGood ⟨1024+i.val,by omega⟩ := by decide +kernel

theorem DartGood_17 : ∀i : Fin 64,DartGood ⟨1088+i.val,by omega⟩ := by decide +kernel

theorem DartGood_18 : ∀i : Fin 64,DartGood ⟨1152+i.val,by omega⟩ := by decide +kernel

theorem DartGood_19 : ∀i : Fin 64,DartGood ⟨1216+i.val,by omega⟩ := by decide +kernel

end PlanarHom.ColoringCrossMacroRows
