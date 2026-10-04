import PlanarHom.ListPairSublistOrder

/-! NEW exact full-row ranks inside and between literal outgoing blocks. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
open ListPairSublistOrder

 theorem edgeBlock_sublist_visitRow (g : MixedCode) (bits : List Bool) {v e : ℕ}
    (he : e∈orderedOutgoing g bits v) : (edgeBlock g bits e).Sublist (visitRow g bits v) := by
  exact (member_flatMap_sublist (edgeBlock g bits) he).trans
    ((List.sublist_append_left _ (loopRow g v)).trans (List.sublist_append_left _ (parentRow g v)))

 theorem localRank_lt_of_pair_sublist (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) {a b : Dart}
    (h : [a,b].Sublist (visitRow g bits v)) : localRank g bits v a<localRank g bits v b := by
  have hs:=(rowIndex_pairwise _ (visitRow_nodup g hg bits hv)).sublist h
  exact (List.pairwise_cons.mp hs).1 b (by simp)

 theorem incoming_false_rank_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v e : ℕ} (hv : v<g.vertices) (he : e∈orderedOutgoing g bits v)
    {a : Dart} (ha : a∈incoming g bits e false) :
    localRank g bits v a<localRank g bits v (outward g e) := by
  apply localRank_lt_of_pair_sublist g hg bits hv
  have hpair : [a,outward g e].Sublist (incoming g bits e false++[outward g e]) :=
    pair_across_append ha (by simp)
  exact (hpair.trans (List.sublist_append_left _ (incoming g bits e true))).trans
    (edgeBlock_sublist_visitRow g bits he)

 theorem incoming_true_rank_gt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v e : ℕ} (hv : v<g.vertices) (he : e∈orderedOutgoing g bits v)
    {a : Dart} (ha : a∈incoming g bits e true) :
    localRank g bits v (outward g e)<localRank g bits v a := by
  apply localRank_lt_of_pair_sublist g hg bits hv
  have hpair : [outward g e,a].Sublist ([outward g e]++incoming g bits e true) :=
    pair_across_append (by simp) ha
  have hb:[outward g e,a].Sublist (edgeBlock g bits e) := by
    exact hpair.trans (by simpa only [edgeBlock,List.append_assoc] using
      List.sublist_append_right (incoming g bits e false) ([outward g e]++incoming g bits e true))
  exact hb.trans (edgeBlock_sublist_visitRow g bits he)

 theorem distinct_blocks_rank_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v e f : ℕ} (hv : v<g.vertices)
    (he : e∈orderedOutgoing g bits v) (hf : f∈orderedOutgoing g bits v)
    (hr : (orderedOutgoing g bits v).idxOf e<(orderedOutgoing g bits v).idxOf f)
    {a b : Dart} (ha : a∈edgeBlock g bits e) (hb : b∈edgeBlock g bits f) :
    localRank g bits v a<localRank g bits v b := by
  apply localRank_lt_of_pair_sublist g hg bits hv
  have hp:=(flatMap_sublist (edgeBlock g bits) (pair_of_idxOf_lt _ he hf hr))
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at hp
  exact ((pair_across_append ha hb).trans hp).trans
    ((List.sublist_append_left _ (loopRow g v)).trans (List.sublist_append_left _ (parentRow g v)))

end PlanarHom.PlanarityLRDirect
