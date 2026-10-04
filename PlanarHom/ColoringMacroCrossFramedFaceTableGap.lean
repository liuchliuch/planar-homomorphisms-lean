import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.CrossFramed
private def gapValue_b0 (i : ℕ) : ℕ :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 6335 else 6305) else (if i < 3 then 6307 else 6309)) else (if i < 6 then (if i < 5 then 6311 else 6313) else (if i < 7 then 6315 else 6317))) else (if i < 12 then (if i < 10 then (if i < 9 then 6319 else 6321) else (if i < 11 then 6323 else 6325)) else (if i < 14 then (if i < 13 then 6327 else 6329) else (if i < 15 then 6331 else 6333))))

def gapValue (i : ℕ) : ℕ := gapValue_b0 i

end PlanarHom.ColoringMacroFaces.CrossFramed
