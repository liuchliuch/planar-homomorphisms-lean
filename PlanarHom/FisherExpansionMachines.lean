import PlanarHom.FisherCodeProgram

/-! NEW encoded polynomial runtime for the literal path-and-endloop expansion.
The output graph is computed from ordinary code and finite numeric row lists. -/
namespace PlanarHom.FisherCodeMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
abbrev dartCode := BitEncoding.nat.prod BitEncoding.bool
abbrev rowsCode := dartCode.list.list
abbrev slotCode := BitEncoding.nat.prod BitEncoding.nat
abbrev edgeCode := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)

 theorem fp_getD {A : Type} (ea : BitEncoding A) (d : A) :
    FP (ea.list.prod BitEncoding.nat) ea (fun p=>p.1.getD p.2 d) :=
  (PfaffianList.fp_at ea d).congr (fun _=>by simp [PfaffianList.lookup,List.getD_eq_getElem?_getD])

 theorem fp_flatMap {A B C : Type} (ea : BitEncoding A) (eb : BitEncoding B) (ec : BitEncoding C)
    (f : A→B→List C) (hf : FP (ea.prod eb) ec.list (fun p=>f p.1 p.2)) :
    FP (ea.prod eb.list) ec.list (fun p=>p.2.flatMap (f p.1)) :=
  ((ListContextMachines.fp_mapWithContext ea eb ec.list _ hf).comp
    (ListFlattenMachines.fp_flatten ec)).congr (fun _=>by rfl)

 theorem fp_singleton {A : Type} (ea : BitEncoding A) : FP ea ea.list (fun a=>[a]) :=
  ((fp_id ea).pair (fp_const ea ea.list [])).comp (ListMutationMachines.fp_cons ea)

 theorem fp_slot_eq : FP (slotCode.prod slotCode) BitEncoding.bool (fun p=>decide (p.1=p.2)) := by
  have hl:=fp_fst slotCode slotCode
  have hr:=fp_snd slotCode slotCode
  have ha:=((hl.comp (fp_fst BitEncoding.nat BitEncoding.nat)).pair
    (hr.comp (fp_fst BitEncoding.nat BitEncoding.nat))).comp PfaffianList.fp_nat_eq
  have hb:=((hl.comp (fp_snd BitEncoding.nat BitEncoding.nat)).pair
    (hr.comp (fp_snd BitEncoding.nat BitEncoding.nat))).comp PfaffianList.fp_nat_eq
  exact ((ha.pair hb).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr (fun p=>by simp [Prod.ext_iff])

end PlanarHom.FisherCodeMachines

namespace PlanarHom.FisherContourOrder
open Complexity FisherCodeMachines
 theorem fp_computedRows : FP MixedCode.encoding rowsCode computedRows :=
  (PlanarityLRDirect.fp_decidedRows.comp (ListMapMachines.fp_map dartCode.list dartCode.list _
    (ListMapMachines.fp_map dartCode dartCode _ PlanarityRotationCode.fp_reverse))).congr
      (fun _=>by simp [computedRows,List.map_map,Function.comp_def])
end PlanarHom.FisherContourOrder

namespace PlanarHom.FisherExpansionCode
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives FisherCodeMachines
abbrev inputCode := MixedCode.encoding.prod rowsCode
abbrev vertexInputCode := inputCode.prod BitEncoding.nat
abbrev slotInputCode := inputCode.prod slotCode

 theorem fp_row : FP (rowsCode.prod BitEncoding.nat) dartCode.list (fun p=>row p.1 p.2) :=
  fp_getD dartCode.list []

 theorem fp_vertexSlots : FP inputCode slotCode.list (fun p=>vertexSlots p.1 p.2) := by
  have hc:=fp_fst inputCode BitEncoding.nat
  have hv:=fp_snd inputCode BitEncoding.nat
  have hrows:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hr:=(hrows.pair hv).comp fp_row
  have hn:=hr.comp (ListUnaryLengthMachine.fp_length dartCode)
  have hsize:=(hn.pair (fp_const vertexInputCode BitEncoding.unaryNat 2)).comp UnaryArithmeticMachines.fp_add
  have hindices:=hsize.comp UnaryArithmeticMachines.fp_range
  have hpairs:=(hv.pair hindices).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat slotCode id (fp_id slotCode))
  have hg:=fp_fst MixedCode.encoding rowsCode
  have hvs:=(hg.comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  exact ((fp_id inputCode).pair hvs).comp (fp_flatMap inputCode BitEncoding.nat slotCode (fun p v=>(List.range ((row p.2 v).length+2)).map (fun j=>(v,j))) hpairs)

 theorem fp_vertexNumber : FP slotInputCode BitEncoding.nat (fun p=>vertexNumber p.1.1 p.1.2 p.2.1 p.2.2) :=
  ((fp_snd inputCode slotCode).pair ((fp_fst inputCode slotCode).comp fp_vertexSlots)).comp
    (DynamicListIndexMachines.fp_index slotCode fp_slot_eq)

 theorem fp_endpoint : FP (MixedCode.encoding.prod dartCode) BitEncoding.nat (fun p=>endpoint p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding dartCode
  have ha:=fp_snd MixedCode.encoding dartCode
  have hi:=ha.comp (fp_fst BitEncoding.nat BitEncoding.bool)
  have hb:=ha.comp (fp_snd BitEncoding.nat BitEncoding.bool)
  have he:=((hg.comp MixedCode.fp_edges).pair hi).comp (fp_getD edgeCode (0,0,0))
  have hs:=he.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have ht:=(he.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  exact (hb.congr (fun _=>by simp)).ite ht hs

 theorem fp_portNumber : FP (inputCode.prod dartCode) BitEncoding.nat (fun p=>portNumber p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst inputCode dartCode
  have ha:=fp_snd inputCode dartCode
  have hg:=hc.comp (fp_fst MixedCode.encoding rowsCode)
  have hrows:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hv:=(hg.pair ha).comp fp_endpoint
  have hr:=(hrows.pair hv).comp fp_row
  have hi:=(ha.pair hr).comp (DynamicListIndexMachines.fp_index dartCode PlanarityRotationCode.fp_dartEqual)
  exact (hc.pair (hv.pair (hi.comp BinaryArithmetic.fp_successor))).comp fp_vertexNumber

 theorem fp_externalEdges : FP inputCode edgeCode.list (fun p=>externalEdges p.1 p.2) := by
  have hc:=fp_fst inputCode BitEncoding.nat
  have he:=fp_snd inputCode BitEncoding.nat
  have hs:=(hc.pair (he.pair (fp_const vertexInputCode BitEncoding.bool false))).comp fp_portNumber
  have ht:=(hc.pair (he.pair (fp_const vertexInputCode BitEncoding.bool true))).comp fp_portNumber
  have hout:=hs.pair (ht.pair (fp_const vertexInputCode BitEncoding.nat 0))
  have hr:=(fp_fst MixedCode.encoding rowsCode).comp PlanarityLRRawConstraints.fp_edgeRange
  exact ((fp_id inputCode).pair hr).comp
    (ListContextMachines.fp_mapWithContext inputCode BitEncoding.nat edgeCode _ hout)

 theorem fp_localEdges : FP vertexInputCode edgeCode.list (fun p=>localEdges p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst inputCode BitEncoding.nat
  have hv:=fp_snd inputCode BitEncoding.nat
  have hrows:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hd:=((hrows.pair hv).comp fp_row).comp (ListUnaryLengthMachine.fp_length dartCode)
  have hn:=(hd.pair (fp_const vertexInputCode BitEncoding.unaryNat 1)).comp UnaryArithmeticMachines.fp_add
  have hr:=hn.comp UnaryArithmeticMachines.fp_range
  have hcx:=fp_fst vertexInputCode BitEncoding.nat
  have hj:=fp_snd vertexInputCode BitEncoding.nat
  have hctx:=hcx.comp hc
  have hvertex:=hcx.comp hv
  have hs:=(hctx.pair (hvertex.pair hj)).comp fp_vertexNumber
  have ht:=(hctx.pair (hvertex.pair (hj.comp BinaryArithmetic.fp_successor))).comp fp_vertexNumber
  have hitem:=hs.pair (ht.pair (fp_const (vertexInputCode.prod BitEncoding.nat) BitEncoding.nat 0))
  have hpath:=((fp_id vertexInputCode).pair hr).comp
    (ListContextMachines.fp_mapWithContext vertexInputCode BitEncoding.nat edgeCode _ hitem)
  have hzero:=(hc.pair (hv.pair (fp_const vertexInputCode BitEncoding.nat 0))).comp fp_vertexNumber
  have hdb:=((hrows.pair hv).comp fp_row).comp (ListCodecMachines.fp_length dartCode)
  have hlast:=(hc.pair (hv.pair (hdb.comp BinaryArithmetic.fp_successor))).comp fp_vertexNumber
  have hloop₀:=(hzero.pair (hzero.pair (fp_const vertexInputCode BitEncoding.nat 0))).comp (fp_singleton edgeCode)
  have hloop₁:=(hlast.pair (hlast.pair (fp_const vertexInputCode BitEncoding.nat 0))).comp (fp_singleton edgeCode)
  exact (hpath.pair ((hloop₀.pair hloop₁).comp (ListMutationMachines.fp_append edgeCode))).comp
    (ListMutationMachines.fp_append edgeCode)

 theorem fp_internalEdges : FP inputCode edgeCode.list (fun p=>internalEdges p.1 p.2) := by
  have hr:=((fp_fst MixedCode.encoding rowsCode).comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  exact ((fp_id inputCode).pair hr).comp (fp_flatMap inputCode BitEncoding.nat edgeCode (fun p=>localEdges p.1 p.2) fp_localEdges)

 theorem fp_code : FP inputCode MixedCode.encoding (fun p=>code p.1 p.2) := by
  have hn:=fp_vertexSlots.comp (ListUnaryLengthMachine.fp_length slotCode)
  have he:=(fp_externalEdges.pair fp_internalEdges).comp (ListMutationMachines.fp_append edgeCode)
  exact (hn.pair (he.pair (fp_const inputCode MixedCode.unaryEncoding []))).transportOutput (fun _=>rfl)

 theorem fp_computed : FP MixedCode.encoding MixedCode.encoding computed :=
  ((fp_id MixedCode.encoding).pair FisherContourOrder.fp_computedRows).comp fp_code

end PlanarHom.FisherExpansionCode
