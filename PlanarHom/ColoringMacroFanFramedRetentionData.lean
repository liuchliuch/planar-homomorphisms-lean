import PlanarHom.ColoringMacroFanFramedRetentionTable
import PlanarHom.ColoringMacroFanFramedRotation
import PlanarHom.ColoringFanMacroRowsRaw
namespace PlanarHom.ColoringMacroFaces.FanFramed
def numericRow (v : Fin 1058) : List (Fin 5264) := (rawRowValue v.val).map (fun d => ⟨d%5264,Nat.mod_lt _ (by decide)⟩)
def retainedRawRow (v : Fin 1054) : List (ℕ×Bool) := ((rawRowValue v.val).filter (fun d => decide (d/2<2619))).map (fun d => (d/2,decide (d%2=0)))
end PlanarHom.ColoringMacroFaces.FanFramed
