import PlanarHom.ArithmeticCircuitPrimitives
import PlanarHom.MachineOutputTransport
import PlanarHom.ListCodecMachines

/-! # Actual typed list constructor and concatenation with canonical binary headers -/
namespace PlanarHom.ListMutationMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines BinaryArithmetic

/-- Add one framed item and increment the actual binary length header. -/
theorem fp_cons {α : Type} (e : BitEncoding α) :
    FP (e.prod e.list) e.list (fun p : α×List α => p.1::p.2) := by
  have ha := fp_fst e e.list
  have hs := fp_snd e e.list
  have hp := hs.comp (ListCodecMachines.fp_payload e)
  have hl := (hs.comp (ListCodecMachines.fp_length e)).comp fp_successor
  have hword : FP (e.prod e.list) BitEncoding.bits
      (fun p => BitEncoding.frame (e.encode p.1) ++ BitEncoding.frames (p.2.map e.encode)) :=
    (ha.pair hp).transportOutput (fun _ => rfl)
  exact (hl.pair hword).transportOutput (fun p => by
    simp only [BitEncoding.prod,BitEncoding.list,BitEncoding.bits,List.length_cons,
      List.map_cons,BitEncoding.frames,Function.comp_apply,id_eq])

/-- Concatenate two lists by adding their binary lengths and appending their
fully materialized framed payloads. -/
theorem fp_append {α : Type} (e : BitEncoding α) :
    FP (e.list.prod e.list) e.list (fun p : List α×List α => p.1++p.2) := by
  have hl := fp_fst e.list e.list
  have hr := fp_snd e.list e.list
  have hc := (((hl.comp (ListCodecMachines.fp_length e)).pair
    (hr.comp (ListCodecMachines.fp_length e))).comp fp_addition)
  have hp := (((hl.comp (ListCodecMachines.fp_payload e)).pair
    (hr.comp (ListCodecMachines.fp_payload e))).comp PairProjectionMachines.fp_append)
  apply (hc.pair hp).transportOutput
  intro p
  have hframes (xs ys : List Bits) : BitEncoding.frames (xs++ys) =
      BitEncoding.frames xs ++ BitEncoding.frames ys := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [BitEncoding.frames,ih,List.append_assoc]
  simp only [BitEncoding.prod,BitEncoding.list,BitEncoding.bits,List.length_append,
    List.map_append,hframes,Function.comp_apply,id_eq]

end PlanarHom.ListMutationMachines
