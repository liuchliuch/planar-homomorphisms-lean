import PlanarHom.FisherIsingCodeIdentity
import PlanarHom.FisherCubicCodeSignSemantics
import PlanarHom.FisherInheritedRowMachines
import PlanarHom.OccurrenceSkewCodeSemantics

/-! NEW adaptation of the recovered runtime consumer to the inherited finite
Fisher row orientation compiler. The numeric Pfaffian/weight/normalization
program is otherwise unchanged.

The complete ordinary-input Ising value program: computed Fisher graph,
computed Pfaffian orientation, exact reference sign, actual polynomial Pfaffian
elimination and the original fixed-field normalization. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PlanarHom.FKTIsingMachines
open Complexity PairProjectionMachines MultiGraph MultiGraph.Kasteleyn
variable {K:Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension:ℕ}
variable (basis:Module.Basis (Fin dimension) ℚ K)

def matrix (ρ:K) (i j:Bool):K:=if i=j then 1 else ρ

def orientation (g:MixedCode):List ℕ:=FisherInheritedRowCode.orientationLog g

def pfaffianInput (ρ:K) (g:MixedCode):OccurrenceSkewCode.Data K:=
  (FisherCodePipeline.code g,(orientation g,(FisherCodePipeline.isingData ρ g).2))

def matchingValue (ρ:K) (g:MixedCode):K:=
  FisherCubicCode.referenceSign (FisherCodePipeline.intermediate g) (orientation g)*
    PfaffianList.evaluateGrid (OccurrenceSkewCode.grid (pfaffianInput ρ g))

def value (ρ:K) (g:MixedCode):K:=FisherCodePipeline.normalization ρ g*matchingValue ρ g

theorem fp_code:FP MixedCode.encoding MixedCode.encoding FisherCodePipeline.code:=
  FisherExpansionCode.fp_computed.comp FisherCubicCode.fp_code

theorem fp_orientation:FP MixedCode.encoding logCode orientation:=by
  have h:=FisherInheritedRowCode.fp_orientationLog
  exact h.congr (fun g=>rfl)

theorem fp_pfaffianInput (ρ:K):FP MixedCode.encoding (OccurrenceSkewCode.dataEncoding basis) (pfaffianInput ρ):=by
  have hw:=(FisherCodePipeline.fp_isingData basis ρ).comp
    (fp_snd MixedCode.encoding (numberFieldEncoding basis).list)
  exact fp_code.pair (fp_orientation.pair hw)

theorem fp_matchingValue (ρ:K):FP MixedCode.encoding (numberFieldEncoding basis) (matchingValue ρ):=by
  have hs:=(FisherExpansionCode.fp_computed.pair fp_orientation).comp
    (FisherCubicCode.fp_referenceSign basis)
  have hp:=(fp_pfaffianInput basis ρ).comp (OccurrenceSkewCode.fp_evaluate basis)
  exact (hs.pair hp).comp (FixedFieldArithmetic.fp_multiplication basis)

theorem fp_value (ρ:K):FP MixedCode.encoding (numberFieldEncoding basis) (value ρ):=
  ((FisherCodePipeline.fp_normalization basis ρ).pair (fp_matchingValue basis ρ)).comp
    (FixedFieldArithmetic.fp_multiplication basis)

end PlanarHom.FKTIsingMachines
