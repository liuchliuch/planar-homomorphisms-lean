import PlanarHom.ColoringTestMacroRows
noncomputable section
namespace PlanarHom.ColoringTestMacroRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem erase_row : ∀v,(row v).map (fun a=>(a.1.val,a.2))=raw v := by decide +kernel

end PlanarHom.ColoringTestMacroRows
