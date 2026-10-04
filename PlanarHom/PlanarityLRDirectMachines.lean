import PlanarHom.PlanarityRotationCodeMachines

/-! NEW reconstruction. Complete actual raw LR dart-row, cyclic rotation and
face-step code. Runtime is unconditional; a planar embedding is not assumed. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
open PlanarityLRRawConstraints PlanarityLRConstraints PlanarityRotationCode

 theorem fp_parentRow : FP graphIndexCode dartCode.list (fun p=>parentRow p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have he:=PlanarityDepthFirstSearch.fp_parentEdge
  have ha:=((hg.pair he).comp fp_outward).comp fp_reverse
  have hsingle:=(ha.pair (fp_const graphIndexCode dartCode.list [])).comp (ListMutationMachines.fp_cons dartCode)
  have hz:=PlanarityDepthFirstSearch.fp_height.comp RationalCircuits.fp_nat_isZero
  exact hz.ite (fp_const graphIndexCode dartCode.list []) hsingle

 theorem fp_loopRow : FP graphIndexCode dartCode.list (fun p=>loopRow p.1 p.2) := by
  have hc:=fp_fst graphIndexCode BitEncoding.nat
  have he:=fp_snd graphIndexCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.nat)
  have hv:=hc.comp (fp_snd MixedCode.encoding BitEncoding.nat)
  have hedge:=(hg.pair he).comp fp_edge
  have hs:=hedge.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have ht:=(hedge.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have hloop:=(hs.pair ht).comp PfaffianList.fp_nat_eq
  have hvertex:=(hs.pair hv).comp PfaffianList.fp_nat_eq
  have hp : FP (graphIndexCode.prod BitEncoding.nat) BitEncoding.bool
      (fun p=>decide ((edge p.1.1 p.2).1=(edge p.1.1 p.2).2.1 ∧ (edge p.1.1 p.2).1=p.1.2)) :=
    ((hloop.pair hvertex).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr (fun _=>by simp)
  have hr:=(fp_fst MixedCode.encoding BitEncoding.nat).comp fp_edgeRange
  have hfilter:=((fp_id graphIndexCode).pair hr).comp
    (ListContextFilterMachines.fp_filterWithContext graphIndexCode BitEncoding.nat _ hp)
  have hf:=(fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.bool false)
  have ht:=(fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.bool true)
  have htail:=(hf.pair (fp_const BitEncoding.nat dartCode.list [])).comp (ListMutationMachines.fp_cons dartCode)
  have hpair:=(ht.pair htail).comp (ListMutationMachines.fp_cons dartCode)
  exact ((hfilter.comp (ListMapMachines.fp_map BitEncoding.nat dartCode.list _ hpair)).comp
    (ListFlattenMachines.fp_flatten dartCode))

abbrev incomingCode := graphBitsCode.prod (BitEncoding.nat.prod BitEncoding.bool)

 theorem fp_incomingTest : FP (incomingCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p=>decide (branchEdge p.1.1.1 p.2=p.1.2.1 ∧ bitSide p.1.1.2 p.2=p.1.2.2)) := by
  have hc:=fp_fst incomingCode BitEncoding.nat
  have hb:=fp_snd incomingCode BitEncoding.nat
  have hgb:=hc.comp (fp_fst graphBitsCode (BitEncoding.nat.prod BitEncoding.bool))
  have hg:=hgb.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hbits:=hgb.comp (fp_snd MixedCode.encoding BitEncoding.bool.list)
  have hep:=hc.comp (fp_snd graphBitsCode (BitEncoding.nat.prod BitEncoding.bool))
  have he:=hep.comp (fp_fst BitEncoding.nat BitEncoding.bool)
  have hside:=hep.comp (fp_snd BitEncoding.nat BitEncoding.bool)
  have hbranch:=(hg.pair hb).comp fp_branchEdge
  have hbeq:=(hbranch.pair he).comp PfaffianList.fp_nat_eq
  have hbit:=(hbits.pair hb).comp (PfaffianList.fp_at BitEncoding.bool false)
  have hseq:=(hbit.pair hside).comp (fp_bool_gate (fun p=>p.1==p.2))
  exact ((hbeq.pair hseq).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr
    (fun p=>by simp [bitSide,PfaffianList.lookup,List.getD_eq_getElem?_getD,Bool.beq_eq_decide_eq])

 theorem fp_incoming : FP incomingCode dartCode.list (fun p=>incoming p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hgb:=fp_fst graphBitsCode (BitEncoding.nat.prod BitEncoding.bool)
  have hg:=hgb.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hb:=hgb.comp fp_backEvents
  have hfilter:=((fp_id incomingCode).pair hb).comp
    (ListContextFilterMachines.fp_filterWithContext incomingCode BitEncoding.nat _ fp_incomingTest)
  have hrev:=hfilter.comp (ListReverseMachines.fp_reverse BitEncoding.nat)
  exact (hg.pair hrev).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat dartCode _ (fp_outward.comp fp_reverse))

 theorem fp_edgeBlock : FP (graphBitsCode.prod BitEncoding.nat) dartCode.list
    (fun p=>edgeBlock p.1.1 p.1.2 p.2) := by
  let ei:=graphBitsCode.prod BitEncoding.nat
  have hc:=fp_fst graphBitsCode BitEncoding.nat
  have he:=fp_snd graphBitsCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hl:=(hc.pair (he.pair (fp_const ei BitEncoding.bool false))).comp fp_incoming
  have hr:=(hc.pair (he.pair (fp_const ei BitEncoding.bool true))).comp fp_incoming
  have ha:=(hg.pair he).comp fp_outward
  have hm:=(ha.pair (fp_const ei dartCode.list [])).comp (ListMutationMachines.fp_cons dartCode)
  exact (((hl.pair hm).comp (ListMutationMachines.fp_append dartCode)).pair hr).comp
    (ListMutationMachines.fp_append dartCode)

 theorem fp_directRow : FP (graphBitsCode.prod BitEncoding.nat) dartCode.list
    (fun p=>directRow p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst graphBitsCode BitEncoding.nat
  have hv:=fp_snd graphBitsCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hgv:=hg.pair hv
  have hp:=hgv.comp fp_parentRow
  have hl:=hgv.comp fp_loopRow
  have hm:=(hc.pair fp_orderedOutgoing).comp
    (ListContextMachines.fp_mapWithContext graphBitsCode BitEncoding.nat dartCode.list _ fp_edgeBlock)
  have hf:=hm.comp (ListFlattenMachines.fp_flatten dartCode)
  exact (((hp.pair hf).comp (ListMutationMachines.fp_append dartCode)).pair hl).comp
    (ListMutationMachines.fp_append dartCode)

 theorem fp_rowNext : FP (dartCode.list.prod dartCode) dartCode (fun p=>rowNext p.1 p.2) := by
  have hr:=fp_fst dartCode.list dartCode
  have ha:=fp_snd dartCode.list dartCode
  have hi:=(ha.pair hr).comp (DynamicListIndexMachines.fp_index dartCode fp_dartEqual)
  have hs:=hi.comp BinaryArithmetic.fp_successor
  have hn:=hr.comp (ListCodecMachines.fp_length dartCode)
  have hm:=((hs.pair hn).comp BinaryArithmetic.fp_division).comp (fp_snd BitEncoding.nat BitEncoding.nat)
  exact (hr.pair (hm.pair ha)).comp (DynamicListIndexMachines.fp_getDWithDefault dartCode (0,false))

 theorem fp_directRotation : FP (graphBitsCode.prod dartCode) dartCode
    (fun p=>directRotation p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst graphBitsCode dartCode
  have ha:=fp_snd graphBitsCode dartCode
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hv:=(hg.pair ha).comp fp_host
  have hr:=(hc.pair hv).comp fp_directRow
  exact (hr.pair ha).comp fp_rowNext

 theorem fp_faceStep : FP (graphBitsCode.prod dartCode) dartCode
    (fun p=>faceStep p.1.1 p.1.2 p.2) :=
  ((fp_fst graphBitsCode dartCode).pair ((fp_snd graphBitsCode dartCode).comp fp_reverse)).comp fp_directRotation


/-- Ordinary graph input computes its own aligned LR bit vector before any row
or dart query. No externally supplied side assignment occurs in this pipeline. -/
 theorem fp_decidedRow : FP graphIndexCode dartCode.list
    (fun p=>directRow p.1 (decideAligned p.1).2 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hv:=fp_snd MixedCode.encoding BitEncoding.nat
  have hb:=(hg.comp fp_decideAligned).comp (fp_snd BitEncoding.bool BitEncoding.bool.list)
  exact ((hg.pair hb).pair hv).comp fp_directRow

 theorem fp_decidedRows : FP MixedCode.encoding dartCode.list.list
    (fun g=>(List.range g.vertices).map (directRow g (decideAligned g).2)) := by
  have hr:=MixedCode.fp_vertices.comp UnaryArithmeticMachines.fp_range
  exact ((fp_id MixedCode.encoding).pair hr).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat dartCode.list _ fp_decidedRow)

 theorem fp_decidedRotation : FP (MixedCode.encoding.prod dartCode) dartCode
    (fun p=>directRotation p.1 (decideAligned p.1).2 p.2) := by
  have hg:=fp_fst MixedCode.encoding dartCode
  have ha:=fp_snd MixedCode.encoding dartCode
  have hb:=(hg.comp fp_decideAligned).comp (fp_snd BitEncoding.bool BitEncoding.bool.list)
  exact ((hg.pair hb).pair ha).comp fp_directRotation

 theorem fp_decidedFaceStep : FP (MixedCode.encoding.prod dartCode) dartCode
    (fun p=>faceStep p.1 (decideAligned p.1).2 p.2) := by
  have hg:=fp_fst MixedCode.encoding dartCode
  have ha:=fp_snd MixedCode.encoding dartCode
  have hb:=(hg.comp fp_decideAligned).comp (fp_snd BitEncoding.bool BitEncoding.bool.list)
  exact ((hg.pair hb).pair ha).comp fp_faceStep

end PlanarHom.PlanarityLRDirect
