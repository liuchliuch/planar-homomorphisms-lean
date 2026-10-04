import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.FanFramed
private def gapValue_b0 (i : ℕ) : ℕ :=
  (if i < 6 then (if i < 3 then (if i < 1 then 5263 else (if i < 2 then 5239 else 5241)) else (if i < 4 then 5243 else (if i < 5 then 5245 else 5247))) else (if i < 9 then (if i < 7 then 5249 else (if i < 8 then 5251 else 5253)) else (if i < 11 then (if i < 10 then 5255 else 5257) else (if i < 12 then 5259 else 5261))))

def gapValue (i : ℕ) : ℕ := gapValue_b0 i

end PlanarHom.ColoringMacroFaces.FanFramed
