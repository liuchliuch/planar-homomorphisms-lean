import PlanarHom.RepresentedListBatchTrace
import PlanarHom.ContextualOracleBatch

/-! Polynomial actual batch work in input bytes plus literal oracle reply
volume, with independent input-only query-count and query-length bounds. -/
namespace PlanarHom.RepresentedListBatch
open Complexity RepresentedBit

def transcript (oracle:Bits→Bits) (qs:List Bits) : OracleTM2.Transcript :=
  qs.map (fun q=>(q,oracle q))

theorem replyVolume_transcript (oracle:Bits→Bits) (qs:List Bits) :
    replyVolume (transcript oracle qs)=(qs.map (fun q=>(oracle q).length)).sum := by
  simp [replyVolume,transcript,List.map_map,Function.comp_def]

theorem cost_eq (oracle:Bits→Bits) (qs:List Bits) :
    ListMapMachines.mapCost BitEncoding.bits BitEncoding.bits oracle qs=
      3*(qs.map List.length).sum+2*(qs.map (fun q=>(oracle q).length)).sum+5*qs.length := by
  induction qs with
  | nil=>simp [ListMapMachines.mapCost]
  | cons q qs ih=>
    simp only [ListMapMachines.mapCost,List.map_cons,List.sum_cons] at ih ⊢
    simp only [ListMapMachines.itemCost,BitEncoding.bits,id_eq,List.length_cons] at ih ⊢
    omega

theorem list_length_eq (qs:List Bits) :
    (BitEncoding.bits.list.encode qs).length=
      2*(BitEncoding.nat.encode qs.length).length+1+2*(qs.map List.length).sum+qs.length := by
  simp only [BitEncoding.list,BitEncoding.bits,List.map_id,List.length_append,
    BitEncoding.frame_length,BitEncoding.frames_length,List.length_map]
  omega

theorem output_length_le (oracle:Bits→Bits) (qs:List Bits) :
    (BitEncoding.bits.list.encode (qs.map oracle)).length≤
      (BitEncoding.bits.list.encode qs).length+2*replyVolume (transcript oracle qs) := by
  rw [list_length_eq,list_length_eq,replyVolume_transcript]
  simp only [List.length_map,List.map_map,Function.comp_def]
  omega

theorem mapTime_le_volume (oracle:Bits→Bits) (qs:List Bits) :
    ListMapMachines.mapTime BitEncoding.bits BitEncoding.bits oracle qs≤
      10*((BitEncoding.bits.list.encode qs).length+replyVolume (transcript oracle qs)+1) := by
  have hi:=list_length_eq qs
  have ho:=output_length_le oracle qs
  rw [ListMapMachines.mapTime,cost_eq,replyVolume_transcript]
  rw [replyVolume_transcript] at ho
  omega

theorem query_count_le_input (qs:List Bits) : qs.length≤(BitEncoding.bits.list.encode qs).length := by
  have h:=list_length_eq qs
  omega

theorem query_length_le_input (qs:List Bits) (q:Bits) (hq:q∈qs) :
    q.length≤(BitEncoding.bits.list.encode qs).length := by
  have hi:=list_length_eq qs
  have h:=ListMapMachines.mem_le_sum_map List.length hq
  omega

theorem raw_run (oracle:Bits→Bits) (qs:List Bits) :
    ∃steps cost,ListMapMachines.machine.Run oracle
      (ListMapMachines.machine.initial (BitEncoding.bits.list.encode qs))
      (ListMapMachines.machine.final (BitEncoding.bits.list.encode (qs.map oracle)))
      steps cost (transcript oracle qs) ∧
      cost≤10*((BitEncoding.bits.list.encode qs).length+replyVolume (transcript oracle qs)+1) := by
  obtain ⟨s,c,t,hr,hc,hg,ht⟩:=run (ea:=BitEncoding.bits) (eb:=BitEncoding.bits) (f:=oracle) qs
  have he:ListMapMachines.typedOracle BitEncoding.bits BitEncoding.bits oracle=oracle:=by
    funext q
    simp [ListMapMachines.typedOracle,BitEncoding.bits]
  have ht':t=transcript oracle qs:=ht
  rw [he,ht'] at hr
  exact ⟨s,c,hr,hc.trans (mapTime_le_volume oracle qs)⟩

theorem contextual_run (oracle:Bits→Bits) (context:Bits) (qs:List Bits) :
    ∃steps cost,ContextualOracleBatch.machine.Run oracle
      (ContextualOracleBatch.machine.initial ((BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs)))
      (ContextualOracleBatch.machine.final ((BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs.map oracle)))
      steps cost (transcript oracle qs) ∧
      cost≤20*(((BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs)).length+
        replyVolume (transcript oracle qs)+1) := by
  obtain ⟨s,c,hr,hc⟩:=raw_run oracle qs
  have h:=ContextualOracleBatch.run context (BitEncoding.bits.list.encode qs)
    (BitEncoding.bits.list.encode (qs.map oracle)) hr
  refine ⟨_,_,h,?_⟩
  simp only [BitEncoding.prod_length,BitEncoding.bits,id_eq,BitEncoding.frame_length] at hc ⊢
  omega

theorem contextual_output_length_le (oracle:Bits→Bits) (context:Bits) (qs:List Bits) :
    ((BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs.map oracle)).length≤
      ((BitEncoding.bits.prod BitEncoding.bits.list).encode (context,qs)).length+
        2*replyVolume (transcript oracle qs) := by
  have h:=output_length_le oracle qs
  simp only [BitEncoding.prod_length,BitEncoding.bits,id_eq] at h ⊢
  omega

end PlanarHom.RepresentedListBatch
