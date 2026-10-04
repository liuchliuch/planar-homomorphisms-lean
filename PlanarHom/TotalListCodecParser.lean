import PlanarHom.TotalCodecParser
import PlanarHom.OccurrenceKasteleynPivotMachines

/-! NEW total decoder for the existing binary-header list codec. The actual
frame count is materialized before comparing the declared binary header, so
arbitrarily large malformed headers never control a long loop. -/
noncomputable section
namespace PlanarHom.Complexity.BitEncoding.TotalParser
open PairProjectionMachines ArithmeticCircuitPrimitives
variable {A:Type} {ea:BitEncoding A}

def listRun (pa:TotalParser ea) (raw:Bits) : Bool×List A :=
  let h:=RawFrameParser.parse raw
  let ws:=RawFramesParser.parse h.2.2
  let values:=ws.2.map pa.run
  (h.1 && ws.1 && decide (ws.2.length=Computability.decodeNat h.2.1) && values.all Prod.fst,
    values.map Prod.snd)

theorem mapM_decode (pa:TotalParser ea) (ws:List Bits) :
    ws.mapM ea.decode=if (ws.map pa.run).all Prod.fst then some ((ws.map pa.run).map Prod.snd) else none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.mapM_cons,pa.correct,ih]
    cases h:(pa.run w).1 <;> cases ht:(ws.map pa.run).all Prod.fst <;> simp [h,ht]

theorem list_decode_frames (raw:Bits) : ea.list.decode raw=
    (do let h←BitEncoding.unframe raw
        let ws←RawFramesParser.decodeFrames (Computability.decodeNat h.1) h.2
        ws.mapM ea.decode) := by
  unfold BitEncoding.list RawFramesParser.decodeFrames
  cases hh:BitEncoding.unframe raw with
  | none=>simp [hh]
  | some h=>
    cases hs:BitEncoding.unframes (Computability.decodeNat h.1) h.2 with
    | none=>simp [hh,hs,BitEncoding.nat]
    | some p=>by_cases hp:p.2=[] <;> simp [hh,hs,hp,BitEncoding.nat]

theorem listRun_correct (pa:TotalParser ea) (raw:Bits) :
    ea.list.decode raw=if (listRun pa raw).1 then some (listRun pa raw).2 else none := by
  rw [list_decode_frames,RawFrameParser.parse_spec]
  cases hf:(RawFrameParser.parse raw).1
  · simp [listRun,hf]
  · simp only [hf,ite_true,Option.bind_some]
    change (RawFramesParser.decodeFrames (Computability.decodeNat (RawFrameParser.parse raw).2.1)
      (RawFrameParser.parse raw).2.2).bind (List.mapM ea.decode)=_
    rw [RawFramesParser.decodeFrames_spec]
    by_cases hs:(RawFramesParser.parse (RawFrameParser.parse raw).2.2).1=true
    · by_cases hn:(RawFramesParser.parse (RawFrameParser.parse raw).2.2).2.length=
          Computability.decodeNat (RawFrameParser.parse raw).2.1
      · simpa [listRun,hf,hs,hn] using mapM_decode pa (RawFramesParser.parse (RawFrameParser.parse raw).2.2).2
      · simp [listRun,hf,hs,hn]
    · have hh:(RawFramesParser.parse (RawFrameParser.parse raw).2.2).1=false := Bool.eq_false_iff.mpr hs
      simp [listRun,hf,hh]

theorem fp_listRun (pa:TotalParser ea) : FP bits (bool.prod ea.list) (listRun pa) := by
  have hh:=RawFrameParser.fp_parse
  have hfirst:=hh.comp (fp_fst bool (bits.prod bits))
  have hpair:=hh.comp (fp_snd bool (bits.prod bits))
  have hdecl:=(hpair.comp (fp_fst bits bits)).comp (show FP bits BitEncoding.nat Computability.decodeNat from ⟨NatCanonicalizationMachine.decodeComputer⟩)
  have hs:=(hpair.comp (fp_snd bits bits)).comp RawFramesParser.fp_parse
  have hgood:=hs.comp (fp_fst bool bits.list)
  have hwords:=hs.comp (fp_snd bool bits.list)
  have hlen:=(hwords.comp (ListUnaryLengthMachine.fp_length bits)).comp UnaryNatConversionMachine.fp_conversion
  have heq:=(hlen.pair hdecl).comp NatListSumMachines.fp_equal
  have hvalues:=hwords.comp (ListMapMachines.fp_map bits (bool.prod ea) pa.run pa.fp)
  have hall:=hvalues.comp (ListMapMachines.fp_map (bool.prod ea) bool Prod.fst (fp_fst bool ea)) |>.comp
    MultiGraph.Kasteleyn.fp_allBool
  have hok:=((hfirst.pair hgood).comp (fp_bool_gate (fun p=>p.1 && p.2))).pair heq |>.comp (fp_bool_gate (fun p=>p.1 && p.2))
  have hout:=hvalues.comp (ListMapMachines.fp_map (bool.prod ea) ea Prod.snd (fp_snd bool ea))
  exact (((hok.pair hall).comp (fp_bool_gate (fun p=>p.1 && p.2))).pair hout).congr
    (fun raw=>by simp only [Function.comp_apply,Function.comp_def,listRun,List.all_map,List.map_map,id_eq])

def list (pa:TotalParser ea) : TotalParser ea.list := ⟨listRun pa,fp_listRun pa,listRun_correct pa⟩
end PlanarHom.Complexity.BitEncoding.TotalParser
