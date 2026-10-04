import PlanarHom.ColoringMacroWireFramedRetentionTable
import PlanarHom.ColoringMacroWireFramedRotation
import PlanarHom.ColoringWireMacroRows
namespace PlanarHom.ColoringMacroFaces.WireFramed
def numericRow (v : Fin 534) : List (Fin 2646) := (rawRowValue v.val).map (fun d => ⟨d%2646,Nat.mod_lt _ (by decide)⟩)
def retainedRawRow (v : Fin 530) : List (ℕ×Bool) := ((rawRowValue v.val).filter (fun d => decide (d/2<1313))).map (fun d => (d/2,decide (d%2=0)))
end PlanarHom.ColoringMacroFaces.WireFramed
