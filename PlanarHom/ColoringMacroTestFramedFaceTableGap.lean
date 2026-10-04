import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.TestFramed
private def gapValue_b0 (i : ℕ) : ℕ :=
  (if i < 6 then (if i < 3 then (if i < 1 then 569 else (if i < 2 then 545 else 547)) else (if i < 4 then 549 else (if i < 5 then 551 else 553))) else (if i < 9 then (if i < 7 then 555 else (if i < 8 then 557 else 559)) else (if i < 11 then (if i < 10 then 561 else 563) else (if i < 12 then 565 else 567))))

def gapValue (i : ℕ) : ℕ := gapValue_b0 i

end PlanarHom.ColoringMacroFaces.TestFramed
