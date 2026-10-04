import PlanarHom.PlanarityLRRotationRowMachines
import PlanarHom.PlanarityLREventOrder
import PlanarHom.NatWordComparisonMachines
import PlanarHom.DynamicListIndexMachines

/-! NEW reconstruction. Actual encoded computation of branch indices, DFS event
words and their exact deterministic lexicographic ordering. -/
namespace PlanarHom.DynamicListIndexMachines
open Complexity PairProjectionMachines
variable {A : Type}
 theorem fp_getDWithDefault (ea : BitEncoding A) (fixed : A) :
    FP (ea.list.prod (BitEncoding.nat.prod ea)) ea (fun p=>p.1.getD p.2.1 p.2.2) := by
  have hx:=fp_fst ea.list (BitEncoding.nat.prod ea)
  have hp:=fp_snd ea.list (BitEncoding.nat.prod ea)
  have hi:=hp.comp (fp_fst BitEncoding.nat ea)
  have hd:=hp.comp (fp_snd BitEncoding.nat ea)
  have hdrop:=(hi.pair hx).comp (ListDropMachines.fp_drop ea fixed)
  exact ((hdrop.pair hd).comp (PlanarityDepthFirstSearch.fp_headWithDefault ea fixed)).congr (fun p=>by
    simp [List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])
end PlanarHom.DynamicListIndexMachines

namespace PlanarHom.PlanarityLRDirect
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityLRRawConstraints

 theorem fp_rootPath : FP graphIndexCode BitEncoding.nat.list (fun p=>rootPath p.1 p.2) :=
  (((fp_snd MixedCode.encoding BitEncoding.nat).pair PlanarityDepthFirstSearch.fp_ancestorList).comp
    (ListMutationMachines.fp_cons BitEncoding.nat)).comp (ListReverseMachines.fp_reverse BitEncoding.nat)

 theorem fp_branchChild : FP graphIndexCode BitEncoding.nat (fun p=>branchChild p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hs:=fp_source
  have hp:=(hg.pair hs).comp fp_rootPath
  have hi:=fp_targetHeight.comp BinaryArithmetic.fp_successor
  exact (hp.pair (hi.pair hs)).comp (DynamicListIndexMachines.fp_getDWithDefault BitEncoding.nat 0)

 theorem fp_branchEdge : FP graphIndexCode BitEncoding.nat (fun p=>branchEdge p.1 p.2) :=
  ((fp_fst MixedCode.encoding BitEncoding.nat).pair fp_branchChild).comp PlanarityDepthFirstSearch.fp_parentEdge

 theorem fp_treeWord : FP (graphBitsCode.prod BitEncoding.nat) BitEncoding.nat.list
    (fun p=>treeWord p.1.1 p.1.2 p.2) := by
  let ei:=graphBitsCode.prod BitEncoding.nat
  have hc:=fp_fst graphBitsCode BitEncoding.nat
  have hv:=fp_snd graphBitsCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hgv:=hg.pair hv
  have hparent:=hgv.comp PlanarityDepthFirstSearch.fp_parentVertex
  have hedge:=hgv.comp PlanarityDepthFirstSearch.fp_parentEdge
  have hrow:=(hc.pair hparent).comp fp_orderedOutgoing
  have hindex:=(hedge.pair hrow).comp GraphComponentMachines.fp_index
  have hpath:=hgv.comp fp_rootPath
  have hdrop:=((fp_const ei BitEncoding.nat 1).pair hpath).comp (ListDropMachines.fp_drop BitEncoding.nat 0)
  exact (hc.pair hdrop).comp
    (ListContextMachines.fp_mapWithContext graphBitsCode BitEncoding.nat BitEncoding.nat _ hindex)

 theorem fp_backWord : FP (graphBitsCode.prod BitEncoding.nat) BitEncoding.nat.list
    (fun p=>backWord p.1.1 p.1.2 p.2) := by
  let ei:=graphBitsCode.prod BitEncoding.nat
  have hc:=fp_fst graphBitsCode BitEncoding.nat
  have he:=fp_snd graphBitsCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hsource:=(hg.pair he).comp fp_source
  have htree:=(hc.pair hsource).comp fp_treeWord
  have hrow:=(hc.pair hsource).comp fp_orderedOutgoing
  have hi:=(he.pair hrow).comp GraphComponentMachines.fp_index
  have hlast:=(hi.pair (fp_const ei BitEncoding.nat.list [])).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  exact (htree.pair hlast).comp (ListMutationMachines.fp_append BitEncoding.nat)

 theorem fp_eventLE : FP (graphBitsCode.prod (BitEncoding.nat.prod BitEncoding.nat)) BitEncoding.bool
    (fun p=>eventLE p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc:=fp_fst graphBitsCode (BitEncoding.nat.prod BitEncoding.nat)
  have hp:=fp_snd graphBitsCode (BitEncoding.nat.prod BitEncoding.nat)
  have ha:=hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hb:=hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hwa:=(hc.pair ha).comp fp_backWord
  have hwb:=(hc.pair hb).comp fp_backWord
  have hlex:=(hwa.pair hwb).comp NatWordComparisonMachines.fp_lex
  have heq:=(hwa.pair hwb).comp NatWordComparisonMachines.fp_equal
  have hle:=hp.comp fp_le
  have htie:=(heq.pair hle).comp (fp_bool_gate (fun p=>p.1 && p.2))
  exact ((hlex.pair htie).comp (fp_bool_gate (fun p=>p.1 || p.2))).congr
    (fun p=>by simp [eventLE])

 theorem fp_backEvents : FP graphBitsCode BitEncoding.nat.list (fun p=>backEvents p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.bool.list
  have hr:=hg.comp fp_edgeRange
  have hbacks:=(hg.pair hr).comp
    (ListContextFilterMachines.fp_filterWithContext MixedCode.encoding BitEncoding.nat _ fp_isBack)
  have hsort:=ContextNatSortMachines.fp_mergeSort graphBitsCode
    (fun p=>eventLE p.1 p.2) fp_eventLE
    (fun p=>eventLE_total p.1 p.2) (fun p=>eventLE_trans p.1 p.2) (fun p=>eventLE_antisymm p.1 p.2)
  exact ((fp_id graphBitsCode).pair hbacks).comp hsort

end PlanarHom.PlanarityLRDirect
