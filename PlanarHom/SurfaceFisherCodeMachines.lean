import PlanarHom.SurfaceFisherCodeProgram
import PlanarHom.FisherInheritedRowMachines

/-! NEW total encoded Fisher frontend for the supplied rotation rows. -/
set_option maxHeartbeats 1200000
namespace PlanarHom.SurfaceFisherCode
open Complexity PairProjectionMachines FisherCodeMachines
abbrev inputCode := PlanarityRowFaceCode.inputCode

theorem fp_orderRows : FP rowsCode rowsCode orderRows :=
  ListMapMachines.fp_map dartCode.list dartCode.list _
    (ListMapMachines.fp_map dartCode dartCode _ PlanarityRotationCode.fp_reverse)

theorem fp_intermediate : FP inputCode MixedCode.encoding (fun p => intermediate p.1 p.2) :=
  ((fp_fst MixedCode.encoding rowsCode).pair ((fp_snd MixedCode.encoding rowsCode).comp fp_orderRows)).comp
    FisherExpansionCode.fp_code

theorem fp_code : FP inputCode MixedCode.encoding (fun p => code p.1 p.2) :=
  fp_intermediate.comp FisherCubicCode.fp_code

theorem fp_expansionRows : FP inputCode rowsCode (fun p => expansionRows p.1 p.2) := by
  have hc := (fp_fst MixedCode.encoding rowsCode).pair ((fp_snd MixedCode.encoding rowsCode).comp fp_orderRows)
  have hi := (fp_intermediate.comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  exact (hc.pair hi).comp
    (ListContextMachines.fp_mapWithContext FisherInheritedRowCode.graphRowsCode BitEncoding.nat
      dartCode.list _ FisherInheritedRowCode.fp_expansionRow)

theorem fp_inheritedRows : FP inputCode rowsCode (fun p => inheritedRows p.1 p.2) := by
  have hc := fp_intermediate.pair fp_expansionRows
  have hi := (fp_code.comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  exact (hc.pair hi).comp
    (ListContextMachines.fp_mapWithContext FisherInheritedRowCode.graphRowsCode BitEncoding.nat
      dartCode.list _ FisherInheritedRowCode.fp_cubicRow)

theorem fp_orientationLog : FP inputCode MultiGraph.Kasteleyn.logCode (fun p => orientationLog p.1 p.2) := by
  have h := (fp_code.pair fp_inheritedRows).comp PlanarityRowFaceCode.fp_orientationLog
  exact h.congr (fun p => rfl)

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def weights (ρ : K) (g : MixedCode) (rows : Rows) : List K :=
  FisherCubicCode.weights (intermediate g rows)
    (FisherExpansionCode.weights g (orderRows rows) (FisherCodePipeline.isingWeights ρ g))

theorem fp_weights (ρ : K) : FP inputCode (numberFieldEncoding basis).list (fun p => weights ρ p.1 p.2) := by
  have hg := fp_fst MixedCode.encoding rowsCode
  have ho := (fp_snd MixedCode.encoding rowsCode).comp fp_orderRows
  have hx := hg.comp (FisherCodePipeline.fp_isingWeights basis ρ)
  have hw := ((hg.pair ho).pair hx).comp (FisherExpansionCode.fp_weights (numberFieldEncoding basis))
  exact (fp_intermediate.pair hw).comp (FisherCubicCode.fp_weights basis)

end PlanarHom.SurfaceFisherCode
