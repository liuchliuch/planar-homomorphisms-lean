import PlanarHom.PlanarityLREventMachines

/-! NEW reconstruction. Actual original-occurrence dart codecs, reversal,
endpoint lookup and full two-dart materialization. -/
namespace PlanarHom.PlanarityRotationCode
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityLRRawConstraints
abbrev dartCode := BitEncoding.nat.prod BitEncoding.bool

 theorem fp_reverse : FP dartCode dartCode reverse :=
  (fp_fst BitEncoding.nat BitEncoding.bool).pair
    ((fp_snd BitEncoding.nat BitEncoding.bool).comp (fp_bool_unary BitEncoding.bool Bool.not))

 theorem fp_dartEqual : FP (dartCode.prod dartCode) BitEncoding.bool (fun p=>decide (p.1=p.2)) := by
  have hl:=fp_fst dartCode dartCode
  have hr:=fp_snd dartCode dartCode
  have hi:=((hl.comp (fp_fst BitEncoding.nat BitEncoding.bool)).pair
    (hr.comp (fp_fst BitEncoding.nat BitEncoding.bool))).comp PfaffianList.fp_nat_eq
  have hb:=((hl.comp (fp_snd BitEncoding.nat BitEncoding.bool)).pair
    (hr.comp (fp_snd BitEncoding.nat BitEncoding.bool))).comp (fp_bool_gate (fun p=>p.1==p.2))
  exact ((hi.pair hb).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr
    (fun p=>by simp [Bool.beq_eq_decide_eq,Prod.ext_iff])

 theorem fp_host : FP (MixedCode.encoding.prod dartCode) BitEncoding.nat (fun p=>host p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding dartCode
  have ha:=fp_snd MixedCode.encoding dartCode
  have he:=ha.comp (fp_fst BitEncoding.nat BitEncoding.bool)
  have hb:=ha.comp (fp_snd BitEncoding.nat BitEncoding.bool)
  have hedge:=(hg.pair he).comp fp_edge
  have hs:=hedge.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have ht:=(hedge.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have hb' : FP (MixedCode.encoding.prod dartCode) BitEncoding.bool (fun p=>decide (p.2.2=true)) :=
    hb.congr (fun _=>by simp)
  exact hb'.ite hs ht

 theorem fp_outward : FP graphIndexCode dartCode (fun p=>outward p.1 p.2) := by
  have he:=fp_snd MixedCode.encoding BitEncoding.nat
  have hs:=fp_edge.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hflag:=(hs.pair fp_source).comp PfaffianList.fp_nat_eq
  exact he.pair hflag

 theorem fp_allDarts : FP MixedCode.encoding dartCode.list allDarts := by
  have ht:=(fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.bool true)
  have hf:=(fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.bool false)
  have hleft:=fp_edgeRange.comp (ListMapMachines.fp_map BitEncoding.nat dartCode _ ht)
  have hright:=fp_edgeRange.comp (ListMapMachines.fp_map BitEncoding.nat dartCode _ hf)
  exact (hleft.pair hright).comp (ListMutationMachines.fp_append dartCode)

end PlanarHom.PlanarityRotationCode
