import PlanarHom.SurfaceRotationHomology
import PlanarHom.PlanarityRowFaceCodeProgram
import PlanarHom.MixedEvaluationPromises
import PlanarHom.BooleanTensorEasyAssembly

/-! NEW internal supplied-row evaluation model. The dimension bound is derived
from supplied complement data at the public input boundary and is preserved
by the actual component compiler; it is never serialized as advice. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceRowEvaluation
open Complexity PlanarityLRRealization
abbrev Input:=MixedCode×PlanarityRowFaceCode.Rows
abbrev encoding:=PlanarityRowFaceCode.inputCode

def Valid (b u ambient:ℕ) (p:Input) : Prop :=
  ∃hg:p.1.Valid b u,∃R:RotationRows (p.1.toMultiGraph hg),
    PlanarityRowFaceCode.Realizes p.1 hg p.2 R ∧ Module.finrank (ZMod 2) R.Homology≤2*ambient

theorem graph_valid {b u ambient:ℕ} {p:Input} (h:Valid b u ambient p) : p.1.Valid b u := h.choose

variable {C K:Type} [Fintype C] [Field K] [Algebra ℚ K] {dimension b u:ℕ}

def Evaluable (ambient:ℕ) (basis:Module.Basis (Fin dimension) ℚ K)
    (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) : Prop :=
  FP (encoding.restrict (Valid b u ambient)) (numberFieldEncoding basis)
    (fun p:{p:Input // Valid b u ambient p}=>p.val.1.evaluate (graph_valid p.property) M U w)

theorem fp_graph (ambient:ℕ) :
    FP (encoding.restrict (Valid b u ambient)) MixedCode.encoding
      (fun p:{p:Input // Valid b u ambient p}=>p.val.1) :=
  (fp_code_view _ encoding Subtype.val (fun _=>rfl)).comp
    (PairProjectionMachines.fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode)

def PositiveIsingFoundation (ambient:ℕ) : Prop :=
  ∀(K:IntermediateField ℚ ℝ) [FiniteDimensional ℚ K] (dimension:ℕ)
    (basis:Module.Basis (Fin dimension) ℚ K) (ρ:K),0<(ρ:ℝ)→
    Evaluable ambient basis (fun _:Fin 1=>BooleanTensorEasyAssembly.isingMatrix ρ)
      (fun u:Fin 0=>u.elim0) (fun _=>1)

end PlanarHom.SurfaceRowEvaluation
