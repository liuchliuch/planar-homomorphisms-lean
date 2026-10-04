import PlanarHom.PlanarityDepthFirstSearchCodecs

/-! NEW reconstruction. Original-occurrence adjacency lists are actually
computed from raw mixed codes, preserving both loop incidences and parallel IDs. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity PairProjectionMachines

 theorem fp_incidence : FP (BitEncoding.nat.prod (edgeCode.prod BitEncoding.nat)) arcCode.list
    (fun p=>incidence p.1 p.2) := by
  let eq := edgeCode.prod BitEncoding.nat
  let ei := BitEncoding.nat.prod eq
  have hv := fp_fst BitEncoding.nat eq
  have hq := fp_snd BitEncoding.nat eq
  have he := hq.comp (fp_fst edgeCode BitEncoding.nat)
  have hk := hq.comp (fp_snd edgeCode BitEncoding.nat)
  have ha := he.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hb := (he.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have haz := ((ha.pair hk).pair (fp_const ei arcCode.list [])).comp (ListMutationMachines.fp_cons arcCode)
  have hbz := ((hb.pair hk).pair (fp_const ei arcCode.list [])).comp (ListMutationMachines.fp_cons arcCode)
  have haf := ((ha.pair hv).comp PfaffianList.fp_nat_eq).ite hbz (fp_const ei arcCode.list [])
  have hbf := ((hb.pair hv).comp PfaffianList.fp_nat_eq).ite haz (fp_const ei arcCode.list [])
  exact (haf.pair hbf).comp (ListMutationMachines.fp_append arcCode)

 theorem fp_neighbours : FP (MixedCode.encoding.prod BitEncoding.nat) arcCode.list
    (fun p=>neighbours p.1 p.2) := by
  have hg := fp_fst MixedCode.encoding BitEncoding.nat
  have hv := fp_snd MixedCode.encoding BitEncoding.nat
  have hes := (hg.comp MixedCode.fp_edges).comp (ListIndexMachines.fp_zipIdx edgeCode)
  have hm := (hv.pair hes).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat (edgeCode.prod BitEncoding.nat) arcCode.list _ fp_incidence)
  exact hm.comp (ListFlattenMachines.fp_flatten arcCode)

 theorem fp_childTasks :
    FP (MixedCode.encoding.prod (BitEncoding.nat.prod BitEncoding.nat.list)) taskCode.list
      (fun p=>childTasks p.1 p.2.1 p.2.2) := by
  let ec := BitEncoding.nat.list
  have hp := fp_fst ec arcCode
  have ha := fp_snd ec arcCode
  have hv := ha.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have he := ha.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have htask := fp_mkTask (ec.prod arcCode) _ _ _ _ (fp_const _ _ true) hv he hp
  have hg := fp_fst MixedCode.encoding (BitEncoding.nat.prod ec)
  have ht := fp_snd MixedCode.encoding (BitEncoding.nat.prod ec)
  have hvertex := ht.comp (fp_fst BitEncoding.nat ec)
  have hpath := ht.comp (fp_snd BitEncoding.nat ec)
  have hns := (hg.pair hvertex).comp fp_neighbours
  exact (hpath.pair hns).comp (ListContextMachines.fp_mapWithContext ec arcCode taskCode _ htask)

end PlanarHom.PlanarityDepthFirstSearch
