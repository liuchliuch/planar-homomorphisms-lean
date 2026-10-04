import PlanarHom.BooleanQuadraticBounds
import PlanarHom.FixedPowerMachines

/-! NEW complete encoded dense elimination runtime. The full state is bounded
quadratically in the original encoded fold input at every prefix. -/
namespace PlanarHom.BooleanQuadratic
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 theorem fp_run : FP dataCode stateCode run := by
  have hf:=ListFoldMachines.fp_foldl BitEncoding.nat stateCode step fp_step
    (Polynomial.C 300*(Polynomial.X+1)^2) (fun s xs i _=>prefix_state_bound s xs i)
  have hi:=(fp_id dataCode).pair
    ((fp_const dataCode BitEncoding.unaryNat 0).pair (fp_const dataCode BitEncoding.bool false))
  exact ((hi.pair (fp_dimension.comp ZeroOneSharpPMembership.fp_range)).comp hf).congr (fun _=>rfl)

 theorem fp_ofGraph : FP MixedCode.encoding dataCode ofGraph := by
  let eg:=MixedCode.encoding
  let en:=BitEncoding.nat
  let ee:=en.prod (en.prod en)
  have hn:=MixedCode.fp_vertices
  have hline:=fp_mapRange eg BitEncoding.bool _ _ hn (fp_const (eg.prod en) BitEncoding.bool false)
  let ei:=eg.prod en
  let ej:=ei.prod en
  let ec:=ej.prod ee
  have hc:=fp_fst ej ee
  have he:=fp_snd ej ee
  have hij:=fp_fst ei en
  have hj:=fp_snd ei en
  have hg:=hij.comp (fp_fst eg en)
  have hi:=hij.comp (fp_snd eg en)
  have hsrc:=he.comp (fp_fst en (en.prod en))
  have hdst:=(he.comp (fp_snd en (en.prod en))).comp (fp_fst en en)
  have ht:=fp_and ((hsrc.pair (hc.comp hi)).comp NatListSumMachines.fp_equal)
    ((hdst.pair (hc.comp hj)).comp NatListSumMachines.fp_equal)
  have heval:=(((fp_id ej).pair (hg.comp MixedCode.fp_edges)).comp
    (ListContextMachines.fp_mapWithContext ej ee BitEncoding.bool _ ht)).comp fp_xorList
  have hrow:=fp_mapRange ei BitEncoding.bool _ _ ((fp_fst eg en).comp hn) heval
  have hgrid:=fp_mapRange eg BitEncoding.bool.list _ _ hn hrow
  exact ((fp_const eg BitEncoding.bool false).pair (hline.pair hgrid)).congr (fun g=>by
    simp only [ofGraph,Function.comp_apply]
    congr 2
    · simp
)

 theorem fp_unary_sub : FP (BitEncoding.unaryNat.prod BitEncoding.unaryNat)
    BitEncoding.unaryNat (fun p=>p.1-p.2) := by
  have hn:=(fp_fst BitEncoding.unaryNat BitEncoding.unaryNat).comp ZeroOneSharpPMembership.fp_range
  have hk:=(fp_snd BitEncoding.unaryNat BitEncoding.unaryNat).comp UnaryNatConversionMachine.fp_conversion
  exact (((hk.pair hn).comp (ListDropMachines.fp_drop BitEncoding.nat 0)).comp
    (ListUnaryLengthMachine.fp_length BitEncoding.nat)).congr (fun p=>by simp)

 theorem fp_result {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) : FP dataCode (numberFieldEncoding basis) (result (K:=K)) := by
  let ek:=numberFieldEncoding basis
  have hs:=fp_run
  have hq:=hs.comp (fp_fst dataCode (BitEncoding.unaryNat.prod BitEncoding.bool))
  have hm:=hs.comp (fp_snd dataCode (BitEncoding.unaryNat.prod BitEncoding.bool))
  have hp:=hm.comp (fp_fst BitEncoding.unaryNat BitEncoding.bool)
  have hz:=hm.comp (fp_snd BitEncoding.unaryNat BitEncoding.bool)
  have hsigned:=(hq.comp fp_constant).comp (fp_bool_unary ek (BooleanQuadraticGauss.sign (K:=K)))
  have hpower:=((fp_dimension.pair hp).comp fp_unary_sub).comp (FixedPowerMachines.fp_power basis (2:K))
  have hval:=(hsigned.pair hpower).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact ((hz.pair ((fp_const dataCode ek 0).pair hval)).comp (ConditionalMachines.fp_select ek)).congr
    (fun _=>rfl)

 theorem fp_evaluate {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) : FP MixedCode.encoding (numberFieldEncoding basis) (evaluate (K:=K)) :=
  fp_ofGraph.comp (fp_result basis)

end PlanarHom.BooleanQuadratic
