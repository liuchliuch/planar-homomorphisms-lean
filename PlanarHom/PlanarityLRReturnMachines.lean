import PlanarHom.PlanarityLRPrimitiveMachines

/-! NEW reconstruction. Actual raw-graph return lists, lowpoints, outgoing
occurrences and literal two-sided fork blocks in encoded polynomial time. -/
namespace PlanarHom.PlanarityLRRawConstraints
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityLRConstraintBlocks

 theorem fp_returnTest : FP (graphIndexCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p=>isBack p.1.1 p.2 && ancestor p.1.1 (target p.1.1 p.1.2) (source p.1.1 p.2) &&
      decide (targetHeight p.1.1 p.2<PlanarityDepthFirstSearch.height p.1.1 (source p.1.1 p.1.2))) := by
  have hc:=fp_fst graphIndexCode BitEncoding.nat
  have hb:=fp_snd graphIndexCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.nat)
  have hgb:=hg.pair hb
  have hback:=hgb.comp fp_isBack
  have htarget:=hc.comp fp_target
  have hsource:=hgb.comp fp_source
  have hanc:=(hg.pair (htarget.pair hsource)).comp fp_ancestor
  have hbh:=hgb.comp fp_targetHeight
  have hsh:=(hg.pair (hc.comp fp_source)).comp PlanarityDepthFirstSearch.fp_height
  have hlt:=(hbh.pair hsh).comp BinaryArithmetic.fp_comparison
  have hand:=(hback.pair hanc).comp (fp_bool_gate (fun p=>p.1 && p.2))
  exact (hand.pair hlt).comp (fp_bool_gate (fun p=>p.1 && p.2))

 theorem fp_returns : FP graphIndexCode BitEncoding.nat.list (fun p=>returns p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have he:=fp_snd MixedCode.encoding BitEncoding.nat
  have hr:=hg.comp fp_edgeRange
  have hf:=((fp_id graphIndexCode).pair hr).comp
    (ListContextFilterMachines.fp_filterWithContext graphIndexCode BitEncoding.nat _ fp_returnTest)
  have hsingleton:=(he.pair (fp_const graphIndexCode BitEncoding.nat.list [])).comp
    (ListMutationMachines.fp_cons BitEncoding.nat)
  have ht : FP graphIndexCode BitEncoding.bool (fun p=>decide (isTree p.1 p.2=true)):=fp_isTree.congr (fun _=>by simp)
  have hb : FP graphIndexCode BitEncoding.bool (fun p=>decide (isBack p.1 p.2=true)):=fp_isBack.congr (fun _=>by simp)
  exact ht.ite hf (hb.ite hsingleton (fp_const graphIndexCode BitEncoding.nat.list []))

 theorem fp_lowpoint : FP graphIndexCode BitEncoding.nat (fun p=>lowpoint p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hseed:=(hg.pair fp_source).comp PlanarityDepthFirstSearch.fp_height
  have hv:=(hg.pair fp_returns).comp
    (ListContextMachines.fp_mapWithContext MixedCode.encoding BitEncoding.nat BitEncoding.nat _ fp_targetHeight)
  exact (hseed.pair hv).comp fp_foldMin

 theorem fp_outgoingTest : FP (graphIndexCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p=>(isTree p.1.1 p.2 || isBack p.1.1 p.2) && decide (source p.1.1 p.2=p.1.2)) := by
  have hc:=fp_fst graphIndexCode BitEncoding.nat
  have he:=fp_snd graphIndexCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.nat)
  have hv:=hc.comp (fp_snd MixedCode.encoding BitEncoding.nat)
  have hge:=hg.pair he
  have hactive:=((hge.comp fp_isTree).pair (hge.comp fp_isBack)).comp (fp_bool_gate (fun p=>p.1 || p.2))
  have heq:=((hge.comp fp_source).pair hv).comp PfaffianList.fp_nat_eq
  exact (hactive.pair heq).comp (fp_bool_gate (fun p=>p.1 && p.2))

 theorem fp_outgoing : FP graphIndexCode BitEncoding.nat.list (fun p=>outgoing p.1 p.2) := by
  have hr:=(fp_fst MixedCode.encoding BitEncoding.nat).comp fp_edgeRange
  exact ((fp_id graphIndexCode).pair hr).comp
    (ListContextFilterMachines.fp_filterWithContext graphIndexCode BitEncoding.nat _ fp_outgoingTest)

 theorem fp_aboveLowpoint : FP (graphIndexCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p=>decide (lowpoint p.1.1 p.1.2<targetHeight p.1.1 p.2)) := by
  have hc:=fp_fst graphIndexCode BitEncoding.nat
  have hb:=fp_snd graphIndexCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.nat)
  exact ((hc.comp fp_lowpoint).pair ((hg.pair hb).comp fp_targetHeight)).comp BinaryArithmetic.fp_comparison

 theorem fp_forkBlock : FP graphPairCode blockCode (fun p=>forkBlock p.1 p.2.1 p.2.2) := by
  have hg:=fp_fst MixedCode.encoding (BitEncoding.nat.prod BitEncoding.nat)
  have hp:=fp_snd MixedCode.encoding (BitEncoding.nat.prod BitEncoding.nat)
  have h₁:=hg.pair (hp.comp (fp_fst BitEncoding.nat BitEncoding.nat))
  have h₂:=hg.pair (hp.comp (fp_snd BitEncoding.nat BitEncoding.nat))
  have hr₁:=h₁.comp fp_returns
  have hr₂:=h₂.comp fp_returns
  have hf₁:=(h₂.pair hr₁).comp
    (ListContextFilterMachines.fp_filterWithContext graphIndexCode BitEncoding.nat _ fp_aboveLowpoint)
  have hf₂:=(h₁.pair hr₂).comp
    (ListContextFilterMachines.fp_filterWithContext graphIndexCode BitEncoding.nat _ fp_aboveLowpoint)
  exact hf₁.pair hf₂

end PlanarHom.PlanarityLRRawConstraints
