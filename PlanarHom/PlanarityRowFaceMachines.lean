import PlanarHom.PlanarityRowFaceOrbitMachines
import PlanarHom.ListPrefixMachines

/-! NEW reconstruction. Complete raw full-face-table compilation, using the
actual computed LR assignment and finite dart orbits. Root omission is separate. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
open PlanarityRotationCode PlanarityLRDirect PlanarityLRRawConstraints PlanarityLRConstraints

 theorem fp_boundary : FP orbitInputCode dartCode.list (fun p=>boundary p.1.1 p.1.2 p.2) := by
  have hh:=(fp_orbit.pair (fp_const orbitInputCode BitEncoding.nat 1)).comp (ListPrefixMachines.fp_take dartCode)
  have ht:=fp_orbit.comp (ListDecompositionMachines.fp_tail dartCode (0,false))
  have ha:=fp_snd inputCode dartCode
  have hne:=fp_dartEqual.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hne' : FP (dartCode.prod dartCode) BitEncoding.bool (fun p=>p.2 != p.1) :=
    hne.congr (fun p=>by simp [bne,Bool.beq_eq_decide_eq,eq_comm])
  have hp:=(ha.pair ht).comp (ListPrefixMachines.fp_takeWhileWithContext dartCode dartCode (fun a b=>b != a) hne')
  exact (hh.pair hp).comp (ListMutationMachines.fp_append dartCode)

 theorem fp_dartMember : FP (dartCode.prod dartCode.list) BitEncoding.bool
    (fun p=>decide (p.1∈p.2)) := by
  exact (ListPredicateMachines.fp_member dartCode (fun p=>decide (p.1=p.2)) fp_dartEqual).congr
    (fun p=>by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true,decide_eq_true_eq]
      simp [eq_comm])

 theorem fp_representative : FP orbitInputCode dartCode (fun p=>representative p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst orbitInputCode dartCode
  have hb:=fp_snd orbitInputCode dartCode
  have ho:=hc.comp fp_orbit
  have hp:=(hb.pair ho).comp fp_dartMember
  have hg:=(fp_fst inputCode dartCode).comp (fp_fst MixedCode.encoding rowsCode)
  have hd:=hg.comp fp_allDarts
  have hf:=((fp_id orbitInputCode).pair hd).comp
    (ListContextFilterMachines.fp_filterWithContext orbitInputCode dartCode _ hp)
  exact (hf.pair (fp_snd inputCode dartCode)).comp
    (PlanarityDepthFirstSearch.fp_headWithDefault dartCode (0,false))

 theorem fp_representatives : FP inputCode dartCode.list (fun p=>representatives p.1 p.2) := by
  have hp:=(fp_representative.pair (fp_snd inputCode dartCode)).comp fp_dartEqual
  have hd:=(fp_fst MixedCode.encoding rowsCode).comp fp_allDarts
  exact ((fp_id inputCode).pair hd).comp
    (ListContextFilterMachines.fp_filterWithContext inputCode dartCode _ hp)

 theorem fp_fullTable : FP inputCode MultiGraph.Kasteleyn.tableCode (fun p=>fullTable p.1 p.2) := by
  let ep:=dartCode.prod BitEncoding.nat
  have hc:=fp_fst inputCode ep
  have hx:=fp_snd inputCode ep
  have ha:=hx.comp (fp_fst dartCode BitEncoding.nat)
  have hi:=hx.comp (fp_snd dartCode BitEncoding.nat)
  have hb:=(hc.pair ha).comp fp_boundary
  have hv:=hi.pair hb
  have hz:=fp_representatives.comp (ListIndexMachines.fp_zipIdx dartCode)
  exact ((fp_id inputCode).pair hz).comp
    (ListContextMachines.fp_mapWithContext inputCode ep MultiGraph.Kasteleyn.faceCode _ hv)


 theorem fp_rootRepresentative : FP orbitInputCode dartCode
    (fun p=>rootRepresentative p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst orbitInputCode dartCode
  have hb:=fp_snd orbitInputCode dartCode
  have hgb:=hc.comp (fp_fst inputCode dartCode)
  have hg:=hgb.comp (fp_fst MixedCode.encoding rowsCode)
  have ha:=hc.comp (fp_snd inputCode dartCode)
  have hx:=(hg.pair hb).comp PlanarityFaceCode.fp_dartComponent
  have hy:=(hg.pair ha).comp PlanarityFaceCode.fp_dartComponent
  have hp:=(hx.pair hy).comp PfaffianList.fp_nat_eq
  have hrs:=(fp_fst inputCode dartCode).comp fp_representatives
  have hf:=((fp_id orbitInputCode).pair hrs).comp
    (ListContextFilterMachines.fp_filterWithContext orbitInputCode dartCode _ hp)
  exact (hf.pair (fp_snd inputCode dartCode)).comp
    (PlanarityDepthFirstSearch.fp_headWithDefault dartCode (0,false))

 theorem fp_boundedTable : FP inputCode MultiGraph.Kasteleyn.tableCode
    (fun p=>boundedTable p.1 p.2) := by
  let ep:=dartCode.prod BitEncoding.nat
  have hc:=fp_fst inputCode ep
  have hx:=fp_snd inputCode ep
  have ha:=hx.comp (fp_fst dartCode BitEncoding.nat)
  have hi:=hx.comp (fp_snd dartCode BitEncoding.nat)
  have hr:=(hc.pair ha).comp fp_rootRepresentative
  have heq:=(hr.pair ha).comp fp_dartEqual
  have hne : FP (inputCode.prod ep) BitEncoding.bool
      (fun p=>decide (rootRepresentative p.1.1 p.1.2 p.2.1≠p.2.1)) :=
    (heq.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun _=>by simp)
  have hz:=fp_representatives.comp (ListIndexMachines.fp_zipIdx dartCode)
  have hf:=((fp_id inputCode).pair hz).comp
    (ListContextFilterMachines.fp_filterWithContext inputCode ep _ hne)
  have hb:=(hc.pair ha).comp fp_boundary
  exact ((fp_id inputCode).pair hf).comp
    (ListContextMachines.fp_mapWithContext inputCode ep MultiGraph.Kasteleyn.faceCode _ (hi.pair hb))

 theorem fp_orientationLog : FP inputCode MultiGraph.Kasteleyn.logCode (fun p=>orientationLog p.1 p.2) :=
  fp_boundedTable.comp MultiGraph.Kasteleyn.fp_computeOrientation

end PlanarHom.PlanarityRowFaceCode
