import PlanarHom.ColoringEmitterComputedRows
import PlanarHom.PlanarityRowFaceCodeProgram

/-! Exact public machine/semantic join for the literal numeric source rows. -/
noncomputable section
namespace PlanarHom.ColoringEmitter.Canvas
open Complexity ParsimoniousNorOneInThree

theorem compileRows_realizes (f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[]) :
    PlanarityRowFaceCode.Realizes (compile f) (compile_valid f)
      (ColoringEmitterRows.compileRows f) (computedGeometricRows f hf hne) :=
  compileRows_get f hf hne

theorem certified_computedRows :
    FP formulaEncoding PlanarityRowFaceCode.rowsCode ColoringEmitterRows.compileRows ∧
    ∀(f : NumericFormula) (hf:NumericValid f) (hne:f.2≠[]),
      PlanarityRowFaceCode.Realizes (compile f) (compile_valid f)
        (ColoringEmitterRows.compileRows f) (computedGeometricRows f hf hne) :=
  ⟨ColoringEmitterRows.fp_compileRows,compileRows_realizes⟩
end PlanarHom.ColoringEmitter.Canvas
