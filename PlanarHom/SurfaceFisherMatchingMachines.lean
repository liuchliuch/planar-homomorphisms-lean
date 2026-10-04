import PlanarHom.SurfaceFisherMatchingMask
import PlanarHom.FisherCubicMachines

/-! NEW actual encoded FP construction of every representative-matching mask. -/
namespace PlanarHom.SurfaceFisherMatching
open Complexity SurfaceBooleanRows FisherCodeMachines PairProjectionMachines ArithmeticCircuitPrimitives
abbrev contextCode := MixedCode.encoding.prod rowCode
abbrev portInputCode := contextCode.prod slotCode

theorem fp_portBit : FP portInputCode BitEncoding.bool (fun p => portBit p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc := fp_fst contextCode slotCode
  have hg := hc.comp (fp_fst MixedCode.encoding rowCode)
  have hb := hc.comp (fp_snd MixedCode.encoding rowCode)
  have hp := fp_snd contextCode slotCode
  have hv := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hr := (hg.pair hv).comp FisherCubicCode.fp_row
  have ha := (hr.pair hj).comp (fp_getD dartCode (0,false))
  have he := ha.comp (fp_fst BitEncoding.nat BitEncoding.bool)
  exact (hb.pair he).comp fp_bitAt

theorem fp_triangleBit : FP portInputCode BitEncoding.bool (fun p => triangleBit p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc := fp_fst contextCode slotCode
  have hp := fp_snd contextCode slotCode
  have hv := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hs := (hc.pair (hv.pair (hj.comp FisherCubicCode.fp_triangleSrc))).comp fp_portBit
  have ht := (hc.pair (hv.pair (hj.comp FisherCubicCode.fp_triangleDst))).comp fp_portBit
  have hnot := fp_portBit.comp (fp_bool_unary BitEncoding.bool Bool.not)
  exact (((hnot.pair hs).comp (fp_bool_gate (fun p => p.1 && p.2))).pair ht).comp
    (fp_bool_gate (fun p => p.1 && p.2))

theorem fp_mask : FP contextCode rowCode (fun p => mask p.1 p.2) := by
  have hc := fp_fst contextCode BitEncoding.nat
  have hi := fp_snd contextCode BitEncoding.nat
  have hbits := hc.comp (fp_snd MixedCode.encoding rowCode)
  have he := ((hbits.pair hi).comp fp_bitAt).comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hg := fp_fst MixedCode.encoding rowCode
  have hr := hg.comp PlanarityLRRawConstraints.fp_edgeRange
  have hext := ((fp_id contextCode).pair hr).comp
    (ListContextMachines.fp_mapWithContext contextCode BitEncoding.nat BitEncoding.bool _ he)
  let ev := contextCode.prod BitEncoding.nat
  have hcv := fp_fst ev BitEncoding.nat
  have hctx := hcv.comp (fp_fst contextCode BitEncoding.nat)
  have hv := hcv.comp (fp_snd contextCode BitEncoding.nat)
  have hj := fp_snd ev BitEncoding.nat
  have htri := (hctx.pair (hv.pair hj)).comp fp_triangleBit
  have hlocal := ((fp_id ev).pair (fp_const ev BitEncoding.nat.list (List.range 3))).comp
    (ListContextMachines.fp_mapWithContext ev BitEncoding.nat BitEncoding.bool _ htri)
  have hvs := (hg.comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  have hint := ((fp_id contextCode).pair hvs).comp
    (fp_flatMap contextCode BitEncoding.nat BitEncoding.bool (fun p v => (List.range 3).map (triangleBit p.1 p.2 v)) hlocal)
  exact (hext.pair hint).comp (ListMutationMachines.fp_append BitEncoding.bool)

end PlanarHom.SurfaceFisherMatching
