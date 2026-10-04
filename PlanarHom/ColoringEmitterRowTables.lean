import PlanarHom.ColoringEmitterRowMachines
import PlanarHom.ColoringWireMacroRows
import PlanarHom.ColoringCrossMacroRowsRaw
import PlanarHom.ColoringFanMacroRowsRaw
import PlanarHom.ColoringTestMacroRows

/-! The runtime consumes the same frozen coordinate-derived local rows as the
geometric proof. These are finite constants, with the original edge order. -/
namespace PlanarHom.ColoringEmitterRows
open Complexity PositiveBlockProgram ParsimoniousNorOneInThree

def macroTable : RowTable
  | .wire => List.ofFn ColoringWireMacroRows.raw
  | .cross => List.ofFn ColoringCrossMacroRows.raw
  | .fan => List.ofFn ColoringFanMacroRows.raw
  | .test => List.ofFn ColoringTestMacroRows.raw

def compileRows : NumericFormula→List (List Dart) := rows macroTable

theorem fp_compileRows : FP formulaEncoding rowsCode compileRows := fp_rows macroTable

theorem compileRows_length (f : NumericFormula) : (compileRows f).length=(ColoringEmitter.compile f).vertices := by
  simp [compileRows,rows]

theorem compileRows_empty (n : ℕ) : compileRows (n,[])=[] := by
  simp [compileRows,rows,ColoringEmitter.compile]

end PlanarHom.ColoringEmitterRows
