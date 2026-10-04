import PlanarHom.ColoringMacroTestFramedRetentionTable
import PlanarHom.ColoringMacroTestFramedRotation
import PlanarHom.ColoringTestMacroRows
namespace PlanarHom.ColoringMacroFaces.TestFramed
def numericRow (v : Fin 118) : List (Fin 570) := (rawRowValue v.val).map (fun d => ⟨d%570,Nat.mod_lt _ (by decide)⟩)
def retainedRawRow (v : Fin 114) : List (ℕ×Bool) := ((rawRowValue v.val).filter (fun d => decide (d/2<272))).map (fun d => (d/2,decide (d%2=0)))
end PlanarHom.ColoringMacroFaces.TestFramed
