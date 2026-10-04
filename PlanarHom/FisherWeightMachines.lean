import PlanarHom.FisherCubicMachines
import PlanarHom.FixedFieldArithmeticMachines

/-! NEW exact encoded field-weight compiler. Zero and negative weights remain
ordinary values throughout the literal two-stage Fisher construction. -/
namespace PlanarHom.FisherExpansionCode
open Complexity PairProjectionMachines FisherCodeMachines
variable {K : Type} [Zero K] [One K]
 theorem fp_weights (ek : BitEncoding K) :
    FP (inputCode.prod ek.list) ek.list (fun p=>weights p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst inputCode ek.list
  have hx:=fp_snd inputCode ek.list
  have hr:=(hc.comp (fp_fst MixedCode.encoding rowsCode)).comp PlanarityLRRawConstraints.fp_edgeRange
  have hleft:=(hx.pair hr).comp
    (ListContextMachines.fp_mapWithContext ek.list BitEncoding.nat ek _ (fp_getD ek 0))
  have hright:=(hc.comp fp_internalEdges).comp (ListMapMachines.fp_map edgeCode ek _ (fp_const edgeCode ek 1))
  exact (hleft.pair hright).comp (ListMutationMachines.fp_append ek)
end PlanarHom.FisherExpansionCode

namespace PlanarHom.FisherCubicCode
open Complexity PairProjectionMachines FisherCodeMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

 theorem fp_portWeight : FP ((numberFieldEncoding basis).list.prod dartCode) (numberFieldEncoding basis)
    (fun p=>portWeight p.1 p.2) := by
  let ek:=numberFieldEncoding basis
  have hx:=fp_fst ek.list dartCode
  have ha:=fp_snd ek.list dartCode
  have hi:=ha.comp (fp_fst BitEncoding.nat BitEncoding.bool)
  have hb : FP (ek.list.prod dartCode) BitEncoding.bool (fun p=>decide (p.2.2=true)) :=
    (ha.comp (fp_snd BitEncoding.nat BitEncoding.bool)).congr (fun _=>by simp)
  exact hb.ite (fp_const _ ek 1) ((hx.pair hi).comp (fp_getD ek 0))

 theorem fp_weights : FP (MixedCode.encoding.prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis).list (fun p=>weights p.1 p.2) := by
  let ek:=numberFieldEncoding basis
  let ec:=MixedCode.encoding.prod ek.list
  let ev:=ec.prod BitEncoding.nat
  have hctx:=fp_fst ev BitEncoding.nat
  have hj:=fp_snd ev BitEncoding.nat
  have hv:=hctx.comp (fp_snd ec BitEncoding.nat)
  have hc:=hctx.comp (fp_fst ec BitEncoding.nat)
  have hg:=hc.comp (fp_fst MixedCode.encoding ek.list)
  have hx:=hc.comp (fp_snd MixedCode.encoding ek.list)
  have hr:=(hg.pair hv).comp fp_row
  have ha:=(hr.pair (hj.comp fp_triangleSrc)).comp (fp_getD dartCode (0,false))
  have hb:=(hr.pair (hj.comp fp_triangleDst)).comp (fp_getD dartCode (0,false))
  have hwa:=(hx.pair ha).comp (fp_portWeight basis)
  have hwb:=(hx.pair hb).comp (fp_portWeight basis)
  have hf:=(hwa.pair hwb).comp (FixedFieldArithmetic.fp_multiplication basis)
  have hrow:=((fp_id ev).pair (fp_const ev BitEncoding.nat.list (List.range 3))).comp
    (ListContextMachines.fp_mapWithContext ev BitEncoding.nat ek _ hf)
  have hvertices:=((fp_fst MixedCode.encoding ek.list).comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  have hright:=((fp_id ec).pair hvertices).comp
    (fp_flatMap ec BitEncoding.nat ek (fun p v=>(List.range 3).map (fun j=>
      portWeight p.2 ((row p.1 v).getD (triangleSrc j) (0,false))*
      portWeight p.2 ((row p.1 v).getD (triangleDst j) (0,false)))) hrow)
  have herange:=(fp_fst MixedCode.encoding ek.list).comp PlanarityLRRawConstraints.fp_edgeRange
  have hleft:=herange.comp (ListMapMachines.fp_map BitEncoding.nat ek _ (fp_const BitEncoding.nat ek 1))
  exact (hleft.pair hright).comp (ListMutationMachines.fp_append ek)
end PlanarHom.FisherCubicCode

namespace PlanarHom.FisherCodePipeline
open Complexity PairProjectionMachines FisherCodeMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

 theorem fp_intermediate : FP MixedCode.encoding MixedCode.encoding intermediate := FisherExpansionCode.fp_computed
 theorem fp_code : FP MixedCode.encoding MixedCode.encoding code := fp_intermediate.comp FisherCubicCode.fp_code

 theorem fp_isingWeights (ρ : K) : FP MixedCode.encoding (numberFieldEncoding basis).list (isingWeights ρ) :=
  (PlanarityLRRawConstraints.fp_edgeRange.comp (ListMapMachines.fp_map BitEncoding.nat
    (numberFieldEncoding basis) _ (fp_const BitEncoding.nat (numberFieldEncoding basis) ((1-ρ)/(1+ρ))))).congr
      (fun g=>by simp [isingWeights])

 theorem fp_isingData (ρ : K) : FP MixedCode.encoding (MixedCode.encoding.prod (numberFieldEncoding basis).list) (isingData ρ) := by
  have hfirst:=(((fp_id MixedCode.encoding).pair FisherContourOrder.fp_computedRows).pair
    (fp_isingWeights basis ρ)).comp (FisherExpansionCode.fp_weights (numberFieldEncoding basis))
  have hweights:=(fp_intermediate.pair hfirst).comp (FisherCubicCode.fp_weights basis)
  exact fp_code.pair hweights
end PlanarHom.FisherCodePipeline
