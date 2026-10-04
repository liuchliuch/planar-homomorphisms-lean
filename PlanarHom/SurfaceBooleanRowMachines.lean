import PlanarHom.SurfaceBooleanRows
import PlanarHom.DynamicListIndexMachines
import PlanarHom.FisherExpansionMachines

/-! NEW actual framed-list machines for Boolean row operations. -/
namespace PlanarHom.SurfaceBooleanRows
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
abbrev rowCode := BitEncoding.bool.list
abbrev pivotCode := BitEncoding.nat.prod rowCode
abbrev basisCode := pivotCode.list

def longer (r s : Row) : Row := if r.length<s.length then s else r

theorem longer_length (r s : Row) : (longer r s).length=max r.length s.length := by
  unfold longer
  split <;> omega

theorem xorRows_indexed (r s : Row) :
    (longer r s).zipIdx.map (fun p => bitAt r p.2 ^^ bitAt s p.2)=xorRows r s := by
  apply List.ext_getElem
  · simp [longer_length]
  · intro i hi hj
    have he := at_xorRows r s i
    simpa only [bitAt,List.getElem?_eq_getElem hj,Option.getD_some,
      List.getElem_map,List.getElem_zipIdx,Nat.zero_add] using he.symm

theorem fp_bitAt : FP (rowCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p => bitAt p.1 p.2) := FisherCodeMachines.fp_getD BitEncoding.bool false

theorem fp_longer : FP (rowCode.prod rowCode) rowCode (fun p => longer p.1 p.2) := by
  have hr := fp_fst rowCode rowCode
  have hs := fp_snd rowCode rowCode
  have hc := ((hr.comp (ListCodecMachines.fp_length BitEncoding.bool)).pair
    (hs.comp (ListCodecMachines.fp_length BitEncoding.bool))).comp BinaryArithmetic.fp_comparison
  exact hc.ite hs hr

theorem fp_xorRows : FP (rowCode.prod rowCode) rowCode (fun p => xorRows p.1 p.2) := by
  let ec := rowCode.prod rowCode
  let ep := BitEncoding.bool.prod BitEncoding.nat
  have hc := fp_fst ec ep
  have hr := hc.comp (fp_fst rowCode rowCode)
  have hs := hc.comp (fp_snd rowCode rowCode)
  have hi := (fp_snd ec ep).comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have hb := (((hr.pair hi).comp fp_bitAt).pair ((hs.pair hi).comp fp_bitAt)).comp
    (fp_bool_gate (fun p => p.1 ^^ p.2))
  have hl := fp_longer.comp (ListIndexMachines.fp_zipIdx BitEncoding.bool)
  have hm := ((fp_id ec).pair hl).comp
    (ListContextMachines.fp_mapWithContext ec ep BitEncoding.bool _ hb)
  exact hm.congr (fun p => xorRows_indexed p.1 p.2)

theorem fp_pivot : FP rowCode BitEncoding.nat pivot := by
  have heq := fp_bool_gate (fun p => decide (p.1=p.2))
  exact ((fp_const rowCode BitEncoding.bool true).pair (fp_id rowCode)).comp
    (DynamicListIndexMachines.fp_index BitEncoding.bool heq)

theorem fp_clear : FP (rowCode.prod pivotCode) rowCode (fun p => clear p.1 p.2) := by
  have hr := fp_fst rowCode pivotCode
  have hp := fp_snd rowCode pivotCode
  have hi := hp.comp (fp_fst BitEncoding.nat rowCode)
  have hs := hp.comp (fp_snd BitEncoding.nat rowCode)
  have hb : FP (rowCode.prod pivotCode) BitEncoding.bool
      (fun p => decide (bitAt p.1 p.2.1=true)) :=
    ((hr.pair hi).comp fp_bitAt).congr (fun p => by simp)
  exact hb.ite ((hr.pair hs).comp fp_xorRows) hr

end PlanarHom.SurfaceBooleanRows
