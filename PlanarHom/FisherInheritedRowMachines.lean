import PlanarHom.FisherInheritedRowProgram
import PlanarHom.PlanarityRowFaceMachines

/-! NEW actual encoded runtime for inherited path/endloop and canonical
triangle rows, followed by the generic finite face-log compiler. -/
set_option maxHeartbeats 800000

namespace PlanarHom.FisherInheritedRowCode
open Complexity PairProjectionMachines FisherCodeMachines
abbrev graphRowsCode := MixedCode.encoding.prod rowsCode
abbrev rowInputCode := graphRowsCode.prod BitEncoding.nat

 theorem fp_list3 {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B) {a b c : A→B}
    (ha : FP ea eb a) (hb : FP ea eb b) (hc : FP ea eb c) : FP ea eb.list (fun x=>[a x,b x,c x]) :=
  (ha.pair ((hb.pair (hc.comp (fp_singleton eb))).comp (ListMutationMachines.fp_cons eb))).comp
    (ListMutationMachines.fp_cons eb)

 theorem fp_edgeSlots : FP graphRowsCode slotCode.list (fun p=>edgeSlots p.1 p.2) := by
  have hc:=fp_fst graphRowsCode BitEncoding.nat
  have hv:=fp_snd graphRowsCode BitEncoding.nat
  have hrs:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hn:=((hrs.pair hv).comp FisherExpansionCode.fp_row).comp (ListUnaryLengthMachine.fp_length dartCode)
  have hsize:=(hn.pair (fp_const rowInputCode BitEncoding.unaryNat 3)).comp UnaryArithmeticMachines.fp_add
  have hpairs:=(hv.pair (hsize.comp UnaryArithmeticMachines.fp_range)).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat slotCode id (fp_id slotCode))
  have hr:=((fp_fst MixedCode.encoding rowsCode).comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  exact ((fp_id graphRowsCode).pair hr).comp
    (fp_flatMap graphRowsCode BitEncoding.nat slotCode
      (fun p v=>(List.range ((FisherExpansionCode.row p.2 v).length+3)).map (fun j=>(v,j))) hpairs)

 theorem fp_internalNumber : FP (graphRowsCode.prod slotCode) BitEncoding.nat
    (fun p=>internalNumber p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc:=fp_fst graphRowsCode slotCode
  have hslot:=fp_snd graphRowsCode slotCode
  have hg:=hc.comp (fp_fst MixedCode.encoding rowsCode)
  have hm:=(hg.comp MixedCode.fp_edges).comp (ListCodecMachines.fp_length edgeCode)
  have hi:=(hslot.pair (hc.comp fp_edgeSlots)).comp (DynamicListIndexMachines.fp_index slotCode fp_slot_eq)
  exact (hm.pair hi).comp BinaryArithmetic.fp_addition

 theorem fp_expansionRow : FP rowInputCode dartCode.list (fun p=>expansionRow p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst graphRowsCode BitEncoding.nat
  have hw:=fp_snd graphRowsCode BitEncoding.nat
  have hrs:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hslot:=((hc.comp FisherExpansionCode.fp_vertexSlots).pair hw).comp (fp_getD slotCode (0,0))
  have hv:=hslot.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj:=hslot.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hr:=(hrs.pair hv).comp FisherExpansionCode.fp_row
  have hd:=hr.comp (ListCodecMachines.fp_length dartCode)
  have hd₁:=hd.comp BinaryArithmetic.fp_successor
  have hd₂:=hd₁.comp BinaryArithmetic.fp_successor
  have hjprev:=(hj.pair (fp_const rowInputCode BitEncoding.nat 1)).comp BinaryArithmetic.fp_subtraction
  have hnum {f : (MixedCode×Rows)×ℕ→ℕ} (hf : FP rowInputCode BitEncoding.nat f) :
      FP rowInputCode BitEncoding.nat (fun p=>internalNumber p.1.1 p.1.2
        ((FisherExpansionCode.vertexSlots p.1.1 p.1.2).getD p.2 (0,0)).1 (f p)) :=
    (hc.pair (hv.pair hf)).comp fp_internalNumber
  have ht:=fp_const rowInputCode BitEncoding.bool true
  have hf:=fp_const rowInputCode BitEncoding.bool false
  have hstart:=fp_list3 rowInputCode dartCode ((hnum (fp_const rowInputCode BitEncoding.nat 0)).pair ht)
    ((hnum hd₁).pair ht) ((hnum hd₁).pair hf)
  have hend:=fp_list3 rowInputCode dartCode ((hnum hd).pair hf) ((hnum hd₂).pair ht) ((hnum hd₂).pair hf)
  have ha:=((hr.pair hjprev).comp (fp_getD dartCode (0,false))).comp PlanarityRotationCode.fp_reverse
  have hmid:=fp_list3 rowInputCode dartCode ((hnum hjprev).pair hf) ha ((hnum hj).pair ht)
  have hz:=hj.comp RationalCircuits.fp_nat_isZero
  have hl:=(hj.pair hd₁).comp PfaffianList.fp_nat_eq
  exact hz.ite hstart (hl.ite hend hmid)

 theorem fp_expansionRows : FP MixedCode.encoding rowsCode expansionRows := by
  have hctx:=(fp_id MixedCode.encoding).pair FisherContourOrder.fp_computedRows
  have hr:=(FisherExpansionCode.fp_computed.comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  exact (hctx.pair hr).comp
    (ListContextMachines.fp_mapWithContext graphRowsCode BitEncoding.nat dartCode.list _ fp_expansionRow)

 theorem fp_cubicRow : FP rowInputCode dartCode.list (fun p=>cubicRow p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst graphRowsCode BitEncoding.nat
  have hw:=fp_snd graphRowsCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding rowsCode)
  have hrs:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hdiv:=(hw.pair (fp_const rowInputCode BitEncoding.nat 3)).comp BinaryArithmetic.fp_division
  have hv:=hdiv.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hi:=hdiv.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hscan:=(hg.pair hv).comp FisherCubicCode.fp_row
  have ha:=((hscan.pair hi).comp (fp_getD dartCode (0,false))).comp PlanarityRotationCode.fp_reverse
  have hr:=(hrs.pair hv).comp (fp_getD dartCode.list [])
  have hnext:=((hr.pair ha).comp PlanarityLRDirect.fp_rowNext).comp PlanarityRotationCode.fp_reverse
  have hprev:=(((hr.comp (ListReverseMachines.fp_reverse dartCode)).pair ha).comp PlanarityLRDirect.fp_rowNext).comp PlanarityRotationCode.fp_reverse
  have hj:=(hnext.pair hscan).comp (DynamicListIndexMachines.fp_index dartCode PlanarityRotationCode.fp_dartEqual)
  have hk:=(hprev.pair hscan).comp (DynamicListIndexMachines.fp_index dartCode PlanarityRotationCode.fp_dartEqual)
  have hm:=(hg.comp MixedCode.fp_edges).comp (ListCodecMachines.fp_length edgeCode)
  have hthree:=((fp_const rowInputCode BitEncoding.nat 3).pair hv).comp BinaryArithmetic.fp_multiplication
  have hbase:=(hm.pair hthree).comp BinaryArithmetic.fp_addition
  have hej:=(hbase.pair hj).comp BinaryArithmetic.fp_addition
  have hek:=(hbase.pair hk).comp BinaryArithmetic.fp_addition
  have hbj:=((hj.comp FisherCubicCode.fp_triangleSrc).pair hi).comp PfaffianList.fp_nat_eq
  have hbk:=((hk.comp FisherCubicCode.fp_triangleSrc).pair hi).comp PfaffianList.fp_nat_eq
  exact fp_list3 rowInputCode dartCode ha (hek.pair hbk) (hej.pair hbj)

 theorem fp_inheritedRows : FP MixedCode.encoding rowsCode inheritedRows := by
  have hc:=FisherCodePipeline.fp_intermediate.pair fp_expansionRows
  have hr:=(FisherCodePipeline.fp_code.comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  exact (hc.pair hr).comp
    (ListContextMachines.fp_mapWithContext graphRowsCode BitEncoding.nat dartCode.list _ fp_cubicRow)

 theorem fp_orientationLog : FP MixedCode.encoding MultiGraph.Kasteleyn.logCode orientationLog :=
  ((FisherCodePipeline.fp_code.pair fp_inheritedRows).comp PlanarityRowFaceCode.fp_orientationLog).congr (fun _=>rfl)

end PlanarHom.FisherInheritedRowCode
