import PlanarHom.SurfacePlanarComplementProgram

/-! NEW actual FP compilation of all supplied-surface tables from ordinary
planar graph codes. The algorithm is total on every typed code. -/
namespace PlanarHom.SurfacePlanarCompiler
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityRotationCode
open SurfaceRawEmbedding
abbrev grCode:=PlanarityRowFaceCode.inputCode

 theorem fp_disks : FP grCode dartCode.list (fun p=>disks p.1 p.2) := by
  have hc:=fp_fst grCode dartCode
  have ha:=fp_snd grCode dartCode
  have hr:=PlanarityRowFaceCode.fp_rootRepresentative
  have he:=(hr.pair ha).comp PlanarityRotationCode.fp_dartEqual
  have hp : FP (grCode.prod dartCode) BitEncoding.bool
      (fun p=>decide (PlanarityRowFaceCode.rootRepresentative p.1.1 p.1.2 p.2≠p.2)) :=
    (he.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun p=>by simp)
  exact (((fp_id grCode).pair PlanarityRowFaceCode.fp_representatives).comp
    (ListContextFilterMachines.fp_filterWithContext grCode dartCode _ hp)).congr (fun _=>rfl)

 theorem fp_region : FP (grCode.prod dartCode) BitEncoding.nat (fun p=>region p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst grCode dartCode
  have hr:=PlanarityRowFaceCode.fp_representative
  have hroot:=(hc.pair hr).comp PlanarityRowFaceCode.fp_rootRepresentative
  have he:=(hroot.pair hr).comp PlanarityRotationCode.fp_dartEqual
  have hi:=(hr.pair (hc.comp fp_disks)).comp
    (DynamicListIndexMachines.fp_index dartCode PlanarityRotationCode.fp_dartEqual)
  have hp:=hi.comp BinaryArithmetic.fp_successor
  exact ((he.pair ((fp_const _ BitEncoding.nat 0).pair hp)).comp
    (ConditionalMachines.fp_select BitEncoding.nat)).congr (fun p=>by simp [region])

 theorem fp_complement (ambient : ℕ) : FP grCode complementCode (fun p=>complement ambient p.1 p.2) := by
  let en:=BitEncoding.nat
  have hg:=fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode
  have hd:=fp_disks.comp (ListMapMachines.fp_map dartCode en (fun _=>0) (fp_const dartCode en 0))
  have hgen:=((fp_const grCode en ambient).pair hd).comp (ListMutationMachines.fp_cons en)
  let ec:=grCode.prod en
  have hc:=fp_fst grCode en
  have he:=fp_snd grCode en
  have ha (b:Bool):=he.pair (fp_const ec BitEncoding.bool b)
  have hv (b:Bool):=(hc.pair (ha b)).comp fp_region
  have ht:=((hv true).pair (fp_const ec en.list [])).comp (ListMutationMachines.fp_cons en)
  have hpair:=((hv false).pair ht).comp (ListMutationMachines.fp_cons en)
  have hn:=((hg.comp MixedCode.fp_edges).comp
    (ListUnaryLengthMachine.fp_length (en.prod (en.prod en)))).comp UnaryArithmeticMachines.fp_range
  have htable:=(((fp_id grCode).pair hn).comp
    (ListContextMachines.fp_mapWithContext grCode en en.list _ hpair)).comp (ListFlattenMachines.fp_flatten en)
  have hiso:=((hg.comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range).comp
    (ListMapMachines.fp_map en en (fun _=>0) (fp_const en en 0))
  exact (hgen.pair (htable.pair hiso)).transportOutput (fun _=>rfl)

 theorem fp_rows : FP MixedCode.encoding PlanarityRowFaceCode.rowsCode rows :=
  PlanarityLRDirect.fp_decidedRows

 theorem fp_compile (ambient : ℕ) : FP MixedCode.encoding inputCode (compile ambient) := by
  have hgr:=(fp_id MixedCode.encoding).pair fp_rows
  have hc:=hgr.comp (fp_complement ambient)
  exact (fp_id MixedCode.encoding).pair (fp_rows.pair hc)

end PlanarHom.SurfacePlanarCompiler
