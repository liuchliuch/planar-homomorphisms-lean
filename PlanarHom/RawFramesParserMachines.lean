import PlanarHom.RawFramesParser
import PlanarHom.ListDecompositionMachines
import PlanarHom.NatListSumMachines

/-! NEW total frame-list parser machines with an explicit whole-state bound.
The scanner processes one input bit per fold iteration on arbitrary words. -/
namespace PlanarHom.RawFramesParser
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

def stateCode : BitEncoding State := BitEncoding.bool.prod (BitEncoding.bits.prod BitEncoding.bits.list)
def resultCode : BitEncoding Result := BitEncoding.bool.prod BitEncoding.bits.list

def payload (s:State) : ℕ := s.2.1.length+(s.2.2.map List.length).sum+s.2.2.length

theorem state_lower (s:State) : payload s≤(stateCode.encode s).length := by
  simp only [stateCode,BitEncoding.prod_length,BitEncoding.bool,BitEncoding.bits,id_eq,List.length_singleton,
    BitEncoding.list,List.length_append,BitEncoding.frame_length,BitEncoding.frames_length,List.map_map,Function.comp_def,List.map_id,payload]
  omega

theorem state_upper (s:State) : (stateCode.encode s).length≤6*payload s+5 := by
  have h:=ListFlattenMachines.word_length_le_payload BitEncoding.bits s.2.2
  rw [ListFlattenMachines.payloadSize_eq] at h
  change (BitEncoding.bits.list.encode s.2.2).length≤3*(2*(s.2.2.map List.length).sum+s.2.2.length)+1 at h
  simp only [stateCode,BitEncoding.prod_length]
  change 2*1+(2*s.2.1.length+(BitEncoding.bits.list.encode s.2.2).length+1)+1≤6*payload s+5
  unfold payload
  omega

theorem step_payload (s:State) (b:Bool) : payload (step s b)≤payload s+1 := by
  rcases s with ⟨mode,word,words⟩
  cases mode <;> cases b <;> simp [payload,step] <;> omega

theorem fold_payload (xs:Bits) (s:State) : payload (xs.foldl step s)≤payload s+xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons b bs ih =>
    have h:=ih (step s b)
    have hh:=step_payload s b
    simp only [List.foldl_cons,List.length_cons]
    omega

theorem fp_step : FP (stateCode.prod BitEncoding.bool) stateCode (fun p=>step p.1 p.2) := by
  let ec:=stateCode.prod BitEncoding.bool
  have hs:=fp_fst stateCode BitEncoding.bool
  have hb:=fp_snd stateCode BitEncoding.bool
  have hm:=hs.comp (fp_fst BitEncoding.bool (BitEncoding.bits.prod BitEncoding.bits.list))
  have hww:=hs.comp (fp_snd BitEncoding.bool (BitEncoding.bits.prod BitEncoding.bits.list))
  have hw:=hww.comp (fp_fst BitEncoding.bits BitEncoding.bits.list)
  have hws:=hww.comp (fp_snd BitEncoding.bits BitEncoding.bits.list)
  have hdata:=(fp_const ec BitEncoding.bool false).pair (((hb.pair hw).comp RawFrameParser.fp_consBits).pair hws)
  have htag:=(fp_const ec BitEncoding.bool true).pair (hw.pair hws)
  have hend:=(fp_const ec BitEncoding.bool false).pair ((fp_const ec BitEncoding.bits []).pair
    ((hw.pair hws).comp (ListMutationMachines.fp_cons BitEncoding.bits)))
  have hcase:=(hb.pair (htag.pair hend)).comp (ConditionalMachines.fp_select stateCode)
  exact (hm.pair (hdata.pair hcase)).comp (ConditionalMachines.fp_select stateCode)

theorem fp_scan : FP BitEncoding.bits stateCode scan := by
  have hfold:=ListFoldMachines.fp_foldl BitEncoding.bool stateCode step fp_step
    (10*(Polynomial.X+1)) (by
      intro s xs i hi
      have h:=fold_payload (xs.take i) s
      have hu:=state_upper ((xs.take i).foldl step s)
      have hs:=state_lower s
      have hl:=BitEncoding.bool.list_length_le xs
      have he:=BitEncoding.prod_length stateCode BitEncoding.bool.list (s,xs)
      simp only [List.length_take,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one] at *
      omega)
  exact ((fp_const BitEncoding.bits stateCode initial).pair RawBooleanListMachine.fp_boolList).comp hfold

theorem fp_parse : FP BitEncoding.bits resultCode parse := by
  have hs:=fp_scan
  have hm:=hs.comp (fp_fst BitEncoding.bool (BitEncoding.bits.prod BitEncoding.bits.list))
  have hww:=hs.comp (fp_snd BitEncoding.bool (BitEncoding.bits.prod BitEncoding.bits.list))
  have hw:=hww.comp (fp_fst BitEncoding.bits BitEncoding.bits.list)
  have hws:=hww.comp (fp_snd BitEncoding.bits BitEncoding.bits.list)
  have hlen:FP BitEncoding.bits BitEncoding.nat (fun xs:Bits=>xs.length) :=
    (show FP BitEncoding.bits BitEncoding.unaryNat (fun xs:Bits=>xs.length) from ⟨InputLengthMachine.computer BitEncoding.bits⟩).comp UnaryNatConversionMachine.fp_conversion
  have he:=((hw.comp hlen).pair (fp_const BitEncoding.bits BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have hempty:FP BitEncoding.bits BitEncoding.bool (fun raw=>(scan raw).2.1.isEmpty) :=
    he.congr (fun raw=>by simp only [Function.comp_apply]; cases (scan raw).2.1 <;> rfl)
  have hok:=(hm.pair hempty).comp (fp_bool_gate (fun p=>!p.1 && p.2))
  have hrev:=hws.comp (ListReverseMachines.fp_reverse BitEncoding.bits) |>.comp
    (ListMapMachines.fp_map BitEncoding.bits BitEncoding.bits List.reverse RawFrameParser.fp_reverseBits)
  exact hok.pair hrev
end PlanarHom.RawFramesParser
