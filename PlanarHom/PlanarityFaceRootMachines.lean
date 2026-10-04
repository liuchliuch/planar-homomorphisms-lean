import PlanarHom.PlanarityFaceRootProgram
import PlanarHom.OccurrenceKasteleynPeelingMachines

/-! NEW reconstruction. Actual encoded component-root omission and the full
raw graph-to-toggle-log computation. Geometric correctness is proved separately. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PairProjectionMachines PlanarityLRRawConstraints PlanarityRotationCode

 theorem fp_componentRoot : FP graphIndexCode BitEncoding.nat (fun p=>componentRoot p.1 p.2) := by
  have hv:=fp_snd MixedCode.encoding BitEncoding.nat
  have hi:=fp_const graphIndexCode BitEncoding.nat 0
  exact (fp_rootPath.pair (hi.pair hv)).comp
    (DynamicListIndexMachines.fp_getDWithDefault BitEncoding.nat 0)

end PlanarHom.PlanarityLRDirect
namespace PlanarHom.PlanarityFaceCode
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
open PlanarityRotationCode PlanarityLRDirect PlanarityLRRawConstraints PlanarityLRConstraints

 theorem fp_dartComponent : FP (MixedCode.encoding.prod dartCode) BitEncoding.nat
    (fun p=>componentRoot p.1 (host p.1 p.2)) :=
   ((fp_fst MixedCode.encoding dartCode).pair fp_host).comp fp_componentRoot

 theorem fp_rootRepresentative : FP orbitInputCode dartCode
    (fun p=>rootRepresentative p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst orbitInputCode dartCode
  have hb:=fp_snd orbitInputCode dartCode
  have hgb:=hc.comp (fp_fst graphBitsCode dartCode)
  have hg:=hgb.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have ha:=hc.comp (fp_snd graphBitsCode dartCode)
  have hx:=(hg.pair hb).comp fp_dartComponent
  have hy:=(hg.pair ha).comp fp_dartComponent
  have hp:=(hx.pair hy).comp PfaffianList.fp_nat_eq
  have hrs:=(fp_fst graphBitsCode dartCode).comp fp_representatives
  have hf:=((fp_id orbitInputCode).pair hrs).comp
    (ListContextFilterMachines.fp_filterWithContext orbitInputCode dartCode _ hp)
  exact (hf.pair (fp_snd graphBitsCode dartCode)).comp
    (PlanarityDepthFirstSearch.fp_headWithDefault dartCode (0,false))

 theorem fp_boundedTable : FP graphBitsCode MultiGraph.Kasteleyn.tableCode
    (fun p=>boundedTable p.1 p.2) := by
  let ep:=dartCode.prod BitEncoding.nat
  have hc:=fp_fst graphBitsCode ep
  have hx:=fp_snd graphBitsCode ep
  have ha:=hx.comp (fp_fst dartCode BitEncoding.nat)
  have hi:=hx.comp (fp_snd dartCode BitEncoding.nat)
  have hr:=(hc.pair ha).comp fp_rootRepresentative
  have heq:=(hr.pair ha).comp fp_dartEqual
  have hne : FP (graphBitsCode.prod ep) BitEncoding.bool
      (fun p=>decide (rootRepresentative p.1.1 p.1.2 p.2.1≠p.2.1)) :=
    (heq.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun _=>by simp)
  have hz:=fp_representatives.comp (ListIndexMachines.fp_zipIdx dartCode)
  have hf:=((fp_id graphBitsCode).pair hz).comp
    (ListContextFilterMachines.fp_filterWithContext graphBitsCode ep _ hne)
  have hb:=(hc.pair ha).comp fp_boundary
  exact ((fp_id graphBitsCode).pair hf).comp
    (ListContextMachines.fp_mapWithContext graphBitsCode ep MultiGraph.Kasteleyn.faceCode _ (hi.pair hb))

 theorem fp_computedBoundedTable : FP MixedCode.encoding MultiGraph.Kasteleyn.tableCode computedBoundedTable :=
   ((fp_id MixedCode.encoding).pair (fp_decideAligned.comp (fp_snd BitEncoding.bool BitEncoding.bool.list))).comp
     fp_boundedTable

 theorem fp_orientationLog : FP MixedCode.encoding MultiGraph.Kasteleyn.logCode orientationLog :=
   fp_computedBoundedTable.comp MultiGraph.Kasteleyn.fp_computeOrientation

end PlanarHom.PlanarityFaceCode
