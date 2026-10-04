import Mathlib.Data.Fin.Basic
namespace PlanarHom.ColoringMacroFaces.WireFramed
private def gapValue_b0 (i : ℕ) : ℕ :=
  (if i < 5 then (if i < 2 then (if i < 1 then 2645 else 2627) else (if i < 3 then 2629 else (if i < 4 then 2631 else 2633))) else (if i < 7 then (if i < 6 then 2635 else 2637) else (if i < 8 then 2639 else (if i < 9 then 2641 else 2643))))

def gapValue (i : ℕ) : ℕ := gapValue_b0 i

end PlanarHom.ColoringMacroFaces.WireFramed
