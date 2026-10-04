import PlanarHom.FisherExpansionMachines

/-! NEW unconditional encoded runtime of the canonical three-port triangle
compiler. Occurrence enumeration includes both ends of loops. -/
namespace PlanarHom.FisherCubicCode
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives FisherCodeMachines
abbrev graphVertexCode := MixedCode.encoding.prod BitEncoding.nat

 theorem fp_row : FP graphVertexCode dartCode.list (fun p=>row p.1 p.2) := by
  let ec:=edgeCode.prod BitEncoding.nat
  have hv:=fp_fst BitEncoding.nat ec
  have hq:=fp_snd BitEncoding.nat ec
  have hedge:=hq.comp (fp_fst edgeCode BitEncoding.nat)
  have hi:=hq.comp (fp_snd edgeCode BitEncoding.nat)
  have hs:=hedge.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have ht:=(hedge.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have hb₀:=(hs.pair hv).comp PfaffianList.fp_nat_eq
  have hb₁:=(ht.pair hv).comp PfaffianList.fp_nat_eq
  have ha₀:=(hi.pair (fp_const (BitEncoding.nat.prod ec) BitEncoding.bool false)).comp (fp_singleton dartCode)
  have ha₁:=(hi.pair (fp_const (BitEncoding.nat.prod ec) BitEncoding.bool true)).comp (fp_singleton dartCode)
  have hz:=fp_const (BitEncoding.nat.prod ec) dartCode.list []
  have hf:=((hb₀.ite ha₀ hz).pair (hb₁.ite ha₁ hz)).comp (ListMutationMachines.fp_append dartCode)
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hzipped:=(hg.comp MixedCode.fp_edges).comp (ListIndexMachines.fp_zipIdx edgeCode)
  exact ((fp_snd MixedCode.encoding BitEncoding.nat).pair hzipped).comp
    (fp_flatMap BitEncoding.nat ec dartCode
      (fun v q=>(if q.1.1=v then [(q.2,false)] else [])++(if q.1.2.1=v then [(q.2,true)] else [])) hf)

 theorem fp_portNumber : FP (MixedCode.encoding.prod dartCode) BitEncoding.nat (fun p=>portNumber p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding dartCode
  have ha:=fp_snd MixedCode.encoding dartCode
  have hv:=FisherExpansionCode.fp_endpoint
  have hrow:=(hg.pair hv).comp fp_row
  have hi:=(ha.pair hrow).comp (DynamicListIndexMachines.fp_index dartCode PlanarityRotationCode.fp_dartEqual)
  have hthree:=((fp_const (MixedCode.encoding.prod dartCode) BitEncoding.nat 3).pair hv).comp BinaryArithmetic.fp_multiplication
  exact (hthree.pair hi).comp BinaryArithmetic.fp_addition

 theorem fp_triangleSrc : FP BitEncoding.nat BitEncoding.nat triangleSrc := by
  have hzero:=RationalCircuits.fp_nat_isZero
  have hone:=((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat 1)).comp PfaffianList.fp_nat_eq
  exact hzero.ite (fp_const _ _ 1) (hone.ite (fp_const _ _ 2) (fp_const _ _ 0))

 theorem fp_triangleDst : FP BitEncoding.nat BitEncoding.nat triangleDst := by
  have hzero:=RationalCircuits.fp_nat_isZero
  have hone:=((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat 1)).comp PfaffianList.fp_nat_eq
  exact hzero.ite (fp_const _ _ 2) (hone.ite (fp_const _ _ 0) (fp_const _ _ 1))

 theorem fp_externalEdges : FP MixedCode.encoding edgeCode.list externalEdges := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have he:=fp_snd MixedCode.encoding BitEncoding.nat
  have hs:=(hg.pair (he.pair (fp_const graphVertexCode BitEncoding.bool false))).comp fp_portNumber
  have ht:=(hg.pair (he.pair (fp_const graphVertexCode BitEncoding.bool true))).comp fp_portNumber
  have hf:=hs.pair (ht.pair (fp_const graphVertexCode BitEncoding.nat 0))
  exact ((fp_id MixedCode.encoding).pair PlanarityLRRawConstraints.fp_edgeRange).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat edgeCode _ hf)

 theorem fp_internalEdges : FP MixedCode.encoding edgeCode.list internalEdges := by
  have hv:=fp_fst BitEncoding.nat BitEncoding.nat
  have hj:=fp_snd BitEncoding.nat BitEncoding.nat
  have hbase:=((fp_const slotCode BitEncoding.nat 3).pair hv).comp BinaryArithmetic.fp_multiplication
  have hs:=(hbase.pair (hj.comp fp_triangleSrc)).comp BinaryArithmetic.fp_addition
  have ht:=(hbase.pair (hj.comp fp_triangleDst)).comp BinaryArithmetic.fp_addition
  have hf:=hs.pair (ht.pair (fp_const slotCode BitEncoding.nat 0))
  have hrow:=((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat.list (List.range 3))).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat edgeCode _ hf)
  exact ((MixedCode.fp_vertices.comp UnaryArithmeticMachines.fp_range).comp
    (ListMapMachines.fp_map BitEncoding.nat edgeCode.list _ hrow)).comp (ListFlattenMachines.fp_flatten edgeCode)

 theorem fp_code : FP MixedCode.encoding MixedCode.encoding code := by
  have hn:=((fp_const MixedCode.encoding BitEncoding.unaryNat 3).pair MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_mul
  have he:=(fp_externalEdges.pair fp_internalEdges).comp (ListMutationMachines.fp_append edgeCode)
  exact (hn.pair (he.pair (fp_const MixedCode.encoding MixedCode.unaryEncoding []))).transportOutput (fun _=>rfl)

end PlanarHom.FisherCubicCode
