import PlanarHom.ColoringMacroCrossFramedRetentionTable
import PlanarHom.ColoringMacroCrossFramedRotation
import PlanarHom.ColoringCrossMacroRowsRaw
namespace PlanarHom.ColoringMacroFaces.CrossFramed
def numericRow (v : Fin 1274) : List (Fin 6336) := (rawRowValue v.val).map (fun d => ⟨d%6336,Nat.mod_lt _ (by decide)⟩)
def retainedRawRow (v : Fin 1270) : List (ℕ×Bool) := ((rawRowValue v.val).filter (fun d => decide (d/2<3152))).map (fun d => (d/2,decide (d%2=0)))
end PlanarHom.ColoringMacroFaces.CrossFramed
