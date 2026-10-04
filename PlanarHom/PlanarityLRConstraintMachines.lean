import PlanarHom.PlanarityLRReturnMachines

/-! NEW reconstruction. Actual enumeration and solving of the raw DFS-derived
LR forks and minimal-return alignment equations, including bit-vector output. -/
namespace PlanarHom.PlanarityLRRawConstraints
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityLRConstraintBlocks PlanarityParitySolver

 theorem fp_forkAt : FP (graphIndexCode.prod BitEncoding.nat) blockCode
    (fun p=>forkBlock p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst graphIndexCode BitEncoding.nat
  have he₂:=fp_snd graphIndexCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.nat)
  have he₁:=hc.comp (fp_snd MixedCode.encoding BitEncoding.nat)
  exact (hg.pair (he₁.pair he₂)).comp fp_forkBlock

 theorem fp_forkRow : FP (graphIndexCode.prod BitEncoding.nat) blockCode.list
    (fun p=>((outgoing p.1.1 p.1.2).filter (fun e₂=>decide (e₂≠p.2))).map (forkBlock p.1.1 p.2)) := by
  have hc:=fp_fst graphIndexCode BitEncoding.nat
  have he₁:=fp_snd graphIndexCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.nat)
  have ho:=hc.comp fp_outgoing
  have hne : FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.bool
      (fun p:ℕ×ℕ=>decide (p.2≠p.1)) :=
    (PfaffianList.fp_nat_eq.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun p=>by simp [eq_comm])
  have hfiltered:=(he₁.pair ho).comp
    (ListContextFilterMachines.fp_filterWithContext BitEncoding.nat BitEncoding.nat _ hne)
  exact ((hg.pair he₁).pair hfiltered).comp
    (ListContextMachines.fp_mapWithContext graphIndexCode BitEncoding.nat blockCode _ fp_forkAt)

 theorem fp_vertexForks : FP graphIndexCode blockCode.list
    (fun p=>if PlanarityDepthFirstSearch.height p.1 p.2=0 then [] else
      (outgoing p.1 p.2).flatMap (fun e₁=>
        ((outgoing p.1 p.2).filter (fun e₂=>decide (e₂≠e₁))).map (forkBlock p.1 e₁))) := by
  have hm:=((fp_id graphIndexCode).pair fp_outgoing).comp
    (ListContextMachines.fp_mapWithContext graphIndexCode BitEncoding.nat blockCode.list _ fp_forkRow)
  have hbody:=hm.comp (ListFlattenMachines.fp_flatten blockCode)
  have hz:=PlanarityDepthFirstSearch.fp_height.comp RationalCircuits.fp_nat_isZero
  exact hz.ite (fp_const graphIndexCode blockCode.list []) hbody

 theorem fp_forkBlocks : FP MixedCode.encoding blockCode.list forkBlocks := by
  have hr:=MixedCode.fp_vertices.comp UnaryArithmeticMachines.fp_range
  have hm:=((fp_id MixedCode.encoding).pair hr).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat blockCode.list _ fp_vertexForks)
  exact hm.comp (ListFlattenMachines.fp_flatten blockCode)

 theorem fp_solveLR : FP MixedCode.encoding (BitEncoding.bool.prod assignmentCode) solveLR :=
  fp_forkBlocks.comp fp_decideBlocks

 theorem fp_minimumReturnTest : FP (graphIndexCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p=>decide (targetHeight p.1.1 p.2=lowpoint p.1.1 p.1.2)) := by
  have hc:=fp_fst graphIndexCode BitEncoding.nat
  have hb:=fp_snd graphIndexCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.nat)
  exact (((hg.pair hb).comp fp_targetHeight).pair (hc.comp fp_lowpoint)).comp PfaffianList.fp_nat_eq

 theorem fp_minimumReturns : FP graphIndexCode BitEncoding.nat.list
    (fun p=>minimumReturns p.1 p.2) :=
  ((fp_id graphIndexCode).pair fp_returns).comp
    (ListContextFilterMachines.fp_filterWithContext graphIndexCode BitEncoding.nat _ fp_minimumReturnTest)

 theorem fp_crossPairs : FP (BitEncoding.nat.list.prod BitEncoding.nat.list) alignmentCode.list
    (fun p:List ℕ×List ℕ=>p.1.flatMap (fun b=>p.2.map (fun c=>(b,c)))) := by
  have hys:=fp_fst BitEncoding.nat.list BitEncoding.nat
  have hb:=fp_snd BitEncoding.nat.list BitEncoding.nat
  have hrow:=(hb.pair hys).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat alignmentCode id (fp_id alignmentCode))
  have hl:=fp_fst BitEncoding.nat.list BitEncoding.nat.list
  have hr:=fp_snd BitEncoding.nat.list BitEncoding.nat.list
  have hm:=(hr.pair hl).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat.list BitEncoding.nat alignmentCode.list _ hrow)
  exact hm.comp (ListFlattenMachines.fp_flatten alignmentCode)

 theorem fp_alignmentPairs : FP MixedCode.encoding alignmentCode.list alignmentPairs := by
  have htrees:=((fp_id MixedCode.encoding).pair fp_edgeRange).comp
    (ListContextFilterMachines.fp_filterWithContext MixedCode.encoding BitEncoding.nat _ fp_isTree)
  have hpairs:=(fp_minimumReturns.pair fp_minimumReturns).comp fp_crossPairs
  have hm:=((fp_id MixedCode.encoding).pair htrees).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat alignmentCode.list _ hpairs)
  exact hm.comp (ListFlattenMachines.fp_flatten alignmentCode)

 theorem fp_solveAlignedLR : FP MixedCode.encoding (BitEncoding.bool.prod assignmentCode) solveAlignedLR :=
  (fp_forkBlocks.pair fp_alignmentPairs).comp fp_decideAlignedBlocks

end PlanarHom.PlanarityLRRawConstraints

namespace PlanarHom.PlanarityLRConstraints
open Complexity PairProjectionMachines PlanarityParitySolver PlanarityLRRawConstraints

/-- Complete ordinary raw-code aligned LR decision and occurrence-indexed bits. -/
 theorem fp_decideAligned : FP MixedCode.encoding (BitEncoding.bool.prod BitEncoding.bool.list) decideAligned := by
  have hout:=fp_solveAlignedLR
  have hflag:=hout.comp (fp_fst BitEncoding.bool assignmentCode)
  have hassignment:=hout.comp (fp_snd BitEncoding.bool assignmentCode)
  have he:=fp_snd assignmentCode BitEncoding.nat
  have ha:=fp_fst assignmentCode BitEncoding.nat
  have hl:=(he.pair ha).comp PlanarityParitySolver.fp_lookup
  have hm:=(hassignment.pair fp_edgeRange).comp
    (ListContextMachines.fp_mapWithContext assignmentCode BitEncoding.nat BitEncoding.bool _ hl)
  exact hflag.pair hm

/-- Runtime and the exact proved raw combinatorial acceptance criterion for the
same executable output, without claiming a geometric LR characterization. -/
 theorem certified_decideAligned :
    FP MixedCode.encoding (BitEncoding.bool.prod BitEncoding.bool.list) decideAligned ∧
    ∀ (g:MixedCode) {bt ut:ℕ},g.Valid bt ut→
      ((decideAligned g).1=true ↔ ∃side,PlanarityLRRawConstraints.LRCondition g side) :=
  ⟨fp_decideAligned,fun g _ _ hg=>decideAligned_complete g hg⟩

end PlanarHom.PlanarityLRConstraints
