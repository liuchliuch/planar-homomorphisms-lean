import PlanarHom.SurfaceComponentCode
import PlanarHom.FisherExpansionMachines

/-! NEW actual encoded runtime for supplied-row component extraction. -/
namespace PlanarHom.SurfaceComponentCode
open Complexity PairProjectionMachines FisherCodeMachines
abbrev extractCode := PlanarityRowFaceCode.inputCode.prod BitEncoding.nat.list

theorem fp_edgeIds : FP (MixedCode.encoding.prod BitEncoding.nat.list) BitEncoding.nat.list
    (fun p => edgeIds p.1 p.2) := by
  let ep := edgeCode.prod BitEncoding.nat
  have hx := fp_fst BitEncoding.nat.list ep
  have he := (fp_snd BitEncoding.nat.list ep).comp (fp_fst edgeCode BitEncoding.nat)
  have hb := (hx.pair he).comp GraphComponentMachines.fp_edgeInside
  have hxs := fp_snd MixedCode.encoding BitEncoding.nat.list
  have hes := ((fp_fst MixedCode.encoding BitEncoding.nat.list).comp MixedCode.fp_edges).comp
    (ListIndexMachines.fp_zipIdx edgeCode)
  have hf := (hxs.pair hes).comp (ListContextFilterMachines.fp_filterWithContext BitEncoding.nat.list ep _ hb)
  exact hf.comp (ListMapMachines.fp_map ep BitEncoding.nat Prod.snd (fp_snd edgeCode BitEncoding.nat))

theorem fp_extractRows : FP extractCode PlanarityRowFaceCode.rowsCode (fun p => extractRows p.1.1 p.1.2 p.2) := by
  let ec := PlanarityRowFaceCode.rowsCode.prod BitEncoding.nat.list
  have hids := fp_fst BitEncoding.nat.list dartCode
  have ha := fp_snd BitEncoding.nat.list dartCode
  have he := ha.comp (fp_fst BitEncoding.nat BitEncoding.bool)
  have hbit := ha.comp (fp_snd BitEncoding.nat BitEncoding.bool)
  have hi := (he.pair hids).comp GraphComponentMachines.fp_index
  have hdart := hi.pair hbit
  have hc := fp_fst ec BitEncoding.nat
  have hv := fp_snd ec BitEncoding.nat
  have hrs := hc.comp (fp_fst PlanarityRowFaceCode.rowsCode BitEncoding.nat.list)
  have his := hc.comp (fp_snd PlanarityRowFaceCode.rowsCode BitEncoding.nat.list)
  have hr := (hrs.pair hv).comp (fp_getD dartCode.list [])
  have hrow := (his.pair hr).comp (ListContextMachines.fp_mapWithContext BitEncoding.nat.list dartCode dartCode _ hdart)
  have hinput := fp_fst PlanarityRowFaceCode.inputCode BitEncoding.nat.list
  have hxs := fp_snd PlanarityRowFaceCode.inputCode BitEncoding.nat.list
  have hg := hinput.comp (fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode)
  have hrows := hinput.comp (fp_snd MixedCode.encoding PlanarityRowFaceCode.rowsCode)
  have hedges := (hg.pair hxs).comp fp_edgeIds
  exact ((hrows.pair hedges).pair hxs).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat dartCode.list _ hrow)

theorem fp_extract : FP extractCode PlanarityRowFaceCode.inputCode (fun p => extract p.1.1 p.1.2 p.2) := by
  have hc := fp_fst PlanarityRowFaceCode.inputCode BitEncoding.nat.list
  have hg := hc.comp (fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode)
  have hx := fp_snd PlanarityRowFaceCode.inputCode BitEncoding.nat.list
  exact ((hg.pair hx).comp GraphComponentMachines.fp_extract).pair fp_extractRows

theorem fp_components : FP PlanarityRowFaceCode.inputCode PlanarityRowFaceCode.inputCode.list
    (fun p => components p.1 p.2) := by
  have hp := (fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode).comp GraphComponentMachines.fp_parts
  exact ((fp_id PlanarityRowFaceCode.inputCode).pair hp).comp
    (ListContextMachines.fp_mapWithContext PlanarityRowFaceCode.inputCode BitEncoding.nat.list
      PlanarityRowFaceCode.inputCode _ fp_extract)

end PlanarHom.SurfaceComponentCode
