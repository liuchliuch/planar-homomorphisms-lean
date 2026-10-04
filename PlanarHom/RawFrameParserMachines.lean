import PlanarHom.RawFrameParser
import PlanarHom.ListFlattenMachines
import PlanarHom.ListReverseMachines

/-! NEW genuine bit-costed machines for the total first-frame scanner. Its
entire encoded accumulator grows linearly on every input, valid or malformed. -/
namespace PlanarHom.RawFrameParser
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

def stateCode : BitEncoding State := BitEncoding.bool.prod (BitEncoding.bool.prod (BitEncoding.bits.prod BitEncoding.bits))
def resultCode : BitEncoding Result := BitEncoding.bool.prod (BitEncoding.bits.prod BitEncoding.bits)

theorem fp_listBits : FP BitEncoding.bool.list BitEncoding.bits (id:Bits→Bits) := by
  have hsingle:FP BitEncoding.bool BitEncoding.bits (fun b=>[b]) := fp_bool_unary _ _
  have hbody:=((fp_fst BitEncoding.bits BitEncoding.bool).pair
    ((fp_snd BitEncoding.bits BitEncoding.bool).comp hsingle)).comp fp_append
  have hsem:∀(xs z:Bits),xs.foldl (fun acc b=>acc++[b]) z=z++xs := by
    intro xs
    induction xs with
    | nil=>simp
    | cons b bs ih=>intro z; simp [List.foldl_cons,ih,List.append_assoc]
  have hfold:=ListFoldMachines.fp_foldl BitEncoding.bool BitEncoding.bits (fun acc b=>acc++[b]) hbody
    (Polynomial.X+1) (by
      intro z xs i hi
      rw [hsem]
      have he:=BitEncoding.prod_length BitEncoding.bits BitEncoding.bool.list (z,xs)
      have hl:=BitEncoding.bool.list_length_le xs
      simp only [BitEncoding.bits,id_eq,List.length_append,List.length_take,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] at *
      omega)
  exact (((fp_const BitEncoding.bool.list BitEncoding.bits []).pair (fp_id BitEncoding.bool.list)).comp hfold).congr
    (fun xs=>by simp [hsem])

theorem fp_reverseBits : FP BitEncoding.bits BitEncoding.bits List.reverse :=
  (RawBooleanListMachine.fp_boolList.comp (ListReverseMachines.fp_reverse BitEncoding.bool)).comp fp_listBits

theorem fp_consBits : FP (BitEncoding.bool.prod BitEncoding.bits) BitEncoding.bits
    (fun p=>p.1::p.2) := by
  have hfirst:=(fp_fst BitEncoding.bool BitEncoding.bits).comp
    (fp_bool_unary BitEncoding.bits (fun b=>[b]))
  exact (hfirst.pair (fp_snd BitEncoding.bool BitEncoding.bits)).comp fp_append

theorem fp_step : FP (stateCode.prod BitEncoding.bool) stateCode (fun p=>step p.1 p.2) := by
  let ec:=stateCode.prod BitEncoding.bool
  have hs:=fp_fst stateCode BitEncoding.bool
  have hb:=fp_snd stateCode BitEncoding.bool
  have hd:=hs.comp (fp_fst BitEncoding.bool (BitEncoding.bool.prod (BitEncoding.bits.prod BitEncoding.bits)))
  have hrest:=hs.comp (fp_snd BitEncoding.bool (BitEncoding.bool.prod (BitEncoding.bits.prod BitEncoding.bits)))
  have hm:=hrest.comp (fp_fst BitEncoding.bool (BitEncoding.bits.prod BitEncoding.bits))
  have hwt:=hrest.comp (fp_snd BitEncoding.bool (BitEncoding.bits.prod BitEncoding.bits))
  have hw:=hwt.comp (fp_fst BitEncoding.bits BitEncoding.bits)
  have ht:=hwt.comp (fp_snd BitEncoding.bits BitEncoding.bits)
  have htrue:=fp_const ec BitEncoding.bool true
  have hfalse:=fp_const ec BitEncoding.bool false
  have hword:=(hb.pair hw).comp fp_consBits
  have htail:=(hb.pair ht).comp fp_consBits
  have hdone:=htrue.pair (hm.pair (hw.pair htail))
  have hdata:=hfalse.pair (hfalse.pair (hword.pair ht))
  have htag:=hfalse.pair (htrue.pair (hw.pair ht))
  have hend:=htrue.pair (hfalse.pair (hw.pair ht))
  have hcase:=(hb.pair (htag.pair hend)).comp (ConditionalMachines.fp_select stateCode)
  have hmode:=(hm.pair (hdata.pair hcase)).comp (ConditionalMachines.fp_select stateCode)
  exact (hd.pair (hdone.pair hmode)).comp (ConditionalMachines.fp_select stateCode)

theorem state_size (s:State) : (stateCode.encode s).length=7+2*s.2.2.1.length+s.2.2.2.length := by
  simp [stateCode,BitEncoding.prod_length,BitEncoding.bool,BitEncoding.bits]
  omega

theorem step_size (s:State) (b:Bool) :
    (stateCode.encode (step s b)).length≤(stateCode.encode s).length+2 := by
  rw [state_size,state_size]
  rcases s with ⟨done,mode,w,t⟩
  cases done <;> cases mode <;> cases b <;> simp [step] <;> omega

theorem fold_size (xs:Bits) (s:State) :
    (stateCode.encode (xs.foldl step s)).length≤(stateCode.encode s).length+2*xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons b bs ih =>
    have h:=ih (step s b)
    have hh:=step_size s b
    simp only [List.foldl_cons,List.length_cons]
    omega

theorem fp_scan : FP BitEncoding.bits stateCode scan := by
  have hfold:=ListFoldMachines.fp_foldl BitEncoding.bool stateCode step fp_step
    (3*(Polynomial.X+1)) (by
      intro s xs i hi
      have h:=fold_size (xs.take i) s
      have hl:=BitEncoding.bool.list_length_le xs
      have he:=BitEncoding.prod_length stateCode BitEncoding.bool.list (s,xs)
      simp only [List.length_take,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one] at *
      omega)
  exact ((fp_const BitEncoding.bits stateCode initial).pair RawBooleanListMachine.fp_boolList).comp hfold

theorem fp_parse : FP BitEncoding.bits resultCode parse := by
  have hs:=fp_scan
  have hd:=hs.comp (fp_fst BitEncoding.bool (BitEncoding.bool.prod (BitEncoding.bits.prod BitEncoding.bits)))
  have ht:=hs.comp (fp_snd BitEncoding.bool (BitEncoding.bool.prod (BitEncoding.bits.prod BitEncoding.bits))) |>.comp
    (fp_snd BitEncoding.bool (BitEncoding.bits.prod BitEncoding.bits))
  have hw:=(ht.comp (fp_fst BitEncoding.bits BitEncoding.bits)).comp fp_reverseBits
  have hr:=(ht.comp (fp_snd BitEncoding.bits BitEncoding.bits)).comp fp_reverseBits
  exact hd.pair (hw.pair hr)
end PlanarHom.RawFrameParser
