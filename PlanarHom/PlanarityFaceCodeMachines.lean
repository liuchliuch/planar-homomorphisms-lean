import PlanarHom.PlanarityFaceOrbitMachines
import PlanarHom.ListPrefixMachines

/-! NEW reconstruction. Complete raw full-face-table compilation, using the
actual computed LR assignment and finite dart orbits. Root omission is separate. -/
namespace PlanarHom.PlanarityFaceCode
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
open PlanarityRotationCode PlanarityLRDirect PlanarityLRRawConstraints PlanarityLRConstraints

 theorem fp_boundary : FP orbitInputCode dartCode.list (fun p=>boundary p.1.1 p.1.2 p.2) := by
  have hh:=(fp_orbit.pair (fp_const orbitInputCode BitEncoding.nat 1)).comp (ListPrefixMachines.fp_take dartCode)
  have ht:=fp_orbit.comp (ListDecompositionMachines.fp_tail dartCode (0,false))
  have ha:=fp_snd graphBitsCode dartCode
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
  have hg:=(fp_fst graphBitsCode dartCode).comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hd:=hg.comp fp_allDarts
  have hf:=((fp_id orbitInputCode).pair hd).comp
    (ListContextFilterMachines.fp_filterWithContext orbitInputCode dartCode _ hp)
  exact (hf.pair (fp_snd graphBitsCode dartCode)).comp
    (PlanarityDepthFirstSearch.fp_headWithDefault dartCode (0,false))

 theorem fp_representatives : FP graphBitsCode dartCode.list (fun p=>representatives p.1 p.2) := by
  have hp:=(fp_representative.pair (fp_snd graphBitsCode dartCode)).comp fp_dartEqual
  have hd:=(fp_fst MixedCode.encoding BitEncoding.bool.list).comp fp_allDarts
  exact ((fp_id graphBitsCode).pair hd).comp
    (ListContextFilterMachines.fp_filterWithContext graphBitsCode dartCode _ hp)

 theorem fp_fullTable : FP graphBitsCode MultiGraph.Kasteleyn.tableCode (fun p=>fullTable p.1 p.2) := by
  let ep:=dartCode.prod BitEncoding.nat
  have hc:=fp_fst graphBitsCode ep
  have hx:=fp_snd graphBitsCode ep
  have ha:=hx.comp (fp_fst dartCode BitEncoding.nat)
  have hi:=hx.comp (fp_snd dartCode BitEncoding.nat)
  have hb:=(hc.pair ha).comp fp_boundary
  have hv:=hi.pair hb
  have hz:=fp_representatives.comp (ListIndexMachines.fp_zipIdx dartCode)
  exact ((fp_id graphBitsCode).pair hz).comp
    (ListContextMachines.fp_mapWithContext graphBitsCode ep MultiGraph.Kasteleyn.faceCode _ hv)

 theorem fp_computedTable : FP MixedCode.encoding MultiGraph.Kasteleyn.tableCode computedTable :=
  ((fp_id MixedCode.encoding).pair (fp_decideAligned.comp (fp_snd BitEncoding.bool BitEncoding.bool.list))).comp
    fp_fullTable

/-- Exact unconditional complexity and the complete literal-table equation. -/
 theorem certified_computedTable :
    FP MixedCode.encoding MultiGraph.Kasteleyn.tableCode computedTable ∧
    ∀g, computedTable g=(representatives g (decideAligned g).2).zipIdx.map
      (fun p=>(p.2,boundary g (decideAligned g).2 p.1)) := ⟨fp_computedTable,fun _=>rfl⟩

end PlanarHom.PlanarityFaceCode
