import PlanarHom.ContextNatSortMachines
import PlanarHom.PlanarityLRNestingMachines

/-! NEW reconstruction. Actual deterministic LR nesting order and side-separated
outgoing rows, computed from the ordinary graph and literal returned side bits. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityLRRawConstraints

 theorem fp_chordal : FP graphIndexCode BitEncoding.bool (fun p=>chordal p.1 p.2) := by
  have hm:=((fp_id graphIndexCode).pair fp_returns).comp
    (ListContextMachines.fp_mapWithContext graphIndexCode BitEncoding.nat BitEncoding.bool _ fp_aboveLowpoint)
  exact (hm.comp (ListPredicateMachines.fp_any BitEncoding.bool id (fp_id BitEncoding.bool))).congr
    (fun p=>by simp [chordal,List.any_map])

 theorem fp_nestingDepth : FP graphIndexCode BitEncoding.nat (fun p=>nestingDepth p.1 p.2) := by
  have htwice:=(fp_lowpoint.pair fp_lowpoint).comp BinaryArithmetic.fp_addition
  have hbit:=fp_chordal.comp (fp_bool_unary BitEncoding.nat (fun b=>if b then 1 else 0))
  exact ((htwice.pair hbit).comp BinaryArithmetic.fp_addition).congr (fun p=>by
    simp [nestingDepth,Nat.two_mul])

 theorem fp_nestingLE : FP graphPairCode BitEncoding.bool (fun p=>nestingLE p.1 p.2.1 p.2.2) := by
  have hg:=fp_fst MixedCode.encoding (BitEncoding.nat.prod BitEncoding.nat)
  have hp:=fp_snd MixedCode.encoding (BitEncoding.nat.prod BitEncoding.nat)
  have ha:=hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hb:=hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hda:=(hg.pair ha).comp fp_nestingDepth
  have hdb:=(hg.pair hb).comp fp_nestingDepth
  have hlt:=(hda.pair hdb).comp BinaryArithmetic.fp_comparison
  have heq:=(hda.pair hdb).comp PfaffianList.fp_nat_eq
  have hle:=hp.comp fp_le
  have htie:=(heq.pair hle).comp (fp_bool_gate (fun p=>p.1 && p.2))
  exact ((hlt.pair htie).comp (fp_bool_gate (fun p=>p.1 || p.2))).congr (fun p=>by simp [nestingLE])

 theorem fp_nestingOutgoing : FP graphIndexCode BitEncoding.nat.list
    (fun p=>nestingOutgoing p.1 p.2) := by
  have hsort:=ContextNatSortMachines.fp_mergeSort MixedCode.encoding nestingLE fp_nestingLE
    nestingLE_total nestingLE_trans nestingLE_antisymm
  exact (((fp_fst MixedCode.encoding BitEncoding.nat).pair fp_outgoing).comp hsort)

 theorem fp_orderedOutgoing : FP (graphBitsCode.prod BitEncoding.nat) BitEncoding.nat.list
    (fun p=>orderedOutgoing p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst graphBitsCode BitEncoding.nat
  have hv:=fp_snd graphBitsCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have ho:=(hg.pair hv).comp fp_nestingOutgoing
  have hneg:=fp_edgeSide.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hl:=(hc.pair ho).comp
    (ListContextFilterMachines.fp_filterWithContext graphBitsCode BitEncoding.nat _ hneg)
  have hr:=(hc.pair ho).comp
    (ListContextFilterMachines.fp_filterWithContext graphBitsCode BitEncoding.nat _ fp_edgeSide)
  have hrev:=hl.comp (ListReverseMachines.fp_reverse BitEncoding.nat)
  exact (hrev.pair hr).comp (ListMutationMachines.fp_append BitEncoding.nat)

/-- Exact runtime and literal occurrence-preserving row semantics. -/
 theorem certified_orderedOutgoing :
    FP (graphBitsCode.prod BitEncoding.nat) BitEncoding.nat.list
      (fun p=>orderedOutgoing p.1.1 p.1.2 p.2) ∧
    ∀g bits v,(orderedOutgoing g bits v).Perm (outgoing g v) :=
  ⟨fp_orderedOutgoing,orderedOutgoing_perm⟩

end PlanarHom.PlanarityLRDirect
