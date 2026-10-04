import PlanarHom.PottsSourceInverseRows
import PlanarHom.RadialPottsCoefficientQueryMachine
import PlanarHom.ListReverseMachines

/-! NEW all-input polynomial-time inverse-row serialization and actual radial
coefficient-query circuit. The source rows are ordinary input lists; no graph
embedding, row correctness or geometric property is assumed by these machines. -/
namespace PlanarHom.PottsSourceInverseRows
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityRotationCode

theorem fp_previous : FP (inputCode.prod dartCode) dartCode
    (fun p=>previous p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst inputCode dartCode
  have ha:=fp_snd inputCode dartCode
  have hg:=hc.comp (fp_fst MixedCode.encoding rowsCode)
  have hrs:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hv:=(hg.pair ha).comp fp_host
  have hr:=(hrs.pair hv).comp (FisherCodeMachines.fp_getD dartCode.list [])
  have hrev:=hr.comp (ListReverseMachines.fp_reverse dartCode)
  exact (hrev.pair ha).comp PlanarityLRDirect.fp_rowNext

theorem fp_index : FP dartCode BitEncoding.nat index := by
  have he:=fp_fst BitEncoding.nat BitEncoding.bool
  have htwo:=(he.pair he).comp BinaryArithmetic.fp_addition
  have hb:=(fp_snd BitEncoding.nat BitEncoding.bool).comp
    (fp_bool_unary BitEncoding.nat (fun b=>if b then 1 else 0))
  exact ((htwo.pair hb).comp BinaryArithmetic.fp_addition).congr
    (fun a=>by simp [index,Nat.two_mul])

theorem fp_unindex : FP BitEncoding.nat dartCode unindex := by
  have hd:=((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat 2)).comp
    BinaryArithmetic.fp_division
  have he:=hd.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hr:=hd.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hb:=(hr.pair (fp_const BitEncoding.nat BitEncoding.nat 1)).comp PfaffianList.fp_nat_eq
  exact he.pair hb

theorem fp_edgeCountUnary : FP MixedCode.encoding BitEncoding.unaryNat (fun g=>g.edges.length) :=
  MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length PlanarityDepthFirstSearch.edgeCode)

theorem fp_inverseTable : FP inputCode BitEncoding.nat.list (fun p=>inverseTable p.1 p.2) := by
  have hc:=fp_fst inputCode BitEncoding.nat
  have ha:=(fp_snd inputCode BitEncoding.nat).comp fp_unindex
  have hentry:=((hc.pair ha).comp fp_previous).comp fp_index
  have hm:=(fp_fst MixedCode.encoding rowsCode).comp fp_edgeCountUnary
  have hn:=(hm.pair hm).comp UnaryPolynomialMachines.fp_add
  have hr:=hn.comp UnaryArithmeticMachines.fp_range
  exact (((fp_id inputCode).pair hr).comp
    (ListContextMachines.fp_mapWithContext inputCode BitEncoding.nat BitEncoding.nat _ hentry)).congr
    (fun p=>by simp [inverseTable,Nat.two_mul])

abbrev radialSourceCode := inputCode.prod BitEncoding.unaryNat

theorem fp_radialInput : FP radialSourceCode RadialPotts.Numeric.inputEncoding
    (fun p=>radialInput p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst inputCode BitEncoding.unaryNat
  have hk:=fp_snd inputCode BitEncoding.unaryNat
  have hg:=hc.comp (fp_fst MixedCode.encoding rowsCode)
  have hm:=hg.comp fp_edgeCountUnary
  exact hm.pair (hk.pair (hc.comp fp_inverseTable))

theorem fp_coefficientQuery : FP radialSourceCode PottsCoefficientPrograms.inputEncoding
    (fun p=>RadialPotts.Numeric.coefficientQuery (radialInput p.1.1 p.1.2 p.2)) :=
  fp_radialInput.comp RadialPotts.Numeric.fp_coefficientQuery

end PlanarHom.PottsSourceInverseRows
