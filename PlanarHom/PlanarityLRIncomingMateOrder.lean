import PlanarHom.PlanarityLRIncomingSubtreeBounds

/-! NEW exact reversal of event order for incoming mates in a shared literal
branch and side, proved by their reversed filtered-list placement. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints PlanarityRotationCode
open ListPairSublistOrder

 theorem incoming_sublist_edgeBlock (g : MixedCode) (bits : List Bool) (e : ℕ) (side : Bool) :
    (incoming g bits e side).Sublist (edgeBlock g bits e) := by
  cases side with
  | false => exact (List.sublist_append_left _ [outward g e]).trans (List.sublist_append_left _ _)
  | true => exact List.sublist_append_right _ _

 theorem same_branch_target (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true)
    (he : branchEdge g b=branchEdge g c) : target g b=target g c := by
  exact (branchEdge_spec g hg hb).2.1.symm.trans
    ((congrArg (source g) he).trans (branchEdge_spec g hg hc).2.1)

 theorem incoming_mates_reverse_key_order (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true)
    (he : branchEdge g b=branchEdge g c) (hs : bitSide bits b=bitSide bits c)
    (hr : (backEvents g bits).idxOf b<(backEvents g bits).idxOf c) :
    contourKey g bits (reverse (outward g c))<contourKey g bits (reverse (outward g b)) := by
  let p : ℕ→Bool:=fun e=>decide (branchEdge g e=branchEdge g b ∧ bitSide bits e=bitSide bits b)
  have hbp:p b=true:=by simp [p]
  have hcp:p c=true:=by simp [p,he,hs]
  have hpair:=pair_of_idxOf_lt (backEvents g bits)
    ((mem_backEvents g bits b).mpr hb) ((mem_backEvents g bits c).mpr hc) hr
  have hfilter: [b,c].Sublist ((backEvents g bits).filter p) := by
    simpa only [List.filter_cons,hbp,hcp,ite_true,List.filter_nil] using hpair.filter p
  have hmates:[reverse (outward g c),reverse (outward g b)].Sublist
      (incoming g bits (branchEdge g b) (bitSide bits b)) := by
    simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,List.map_cons,List.map_nil,
      incoming,p] using hfilter.reverse.map (fun e=>reverse (outward g e))
  have hbranch:=branchEdge_spec g hg hb
  have hv:=(source_target_valid g hg (of_decide_eq_true hb).1).2
  have hm:branchEdge g b∈orderedOutgoing g bits (target g b):=by
    simpa only [hbranch.2.1] using treeEdge_mem_orderedOutgoing g hg bits hbranch.1
  have hrow:=hmates.trans ((incoming_sublist_edgeBlock g bits _ _).trans (edgeBlock_sublist_visitRow g bits hm))
  have hi:=localRank_lt_of_pair_sublist g hg bits hv hrow
  have ht:=same_branch_target g hg hb hc he
  unfold contourKey
  rw [host_reverse_outward,host_reverse_outward,← ht]
  exact List.Lex.append_left (·<·) (List.Lex.rel hi) _

 theorem incoming_mates_key_lt_iff (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true)
    (he : branchEdge g b=branchEdge g c) (hs : bitSide bits b=bitSide bits c) :
    contourKey g bits (reverse (outward g b))<contourKey g bits (reverse (outward g c)) ↔
      (backEvents g bits).idxOf c<(backEvents g bits).idxOf b := by
  refine ⟨?_,incoming_mates_reverse_key_order g hg bits hc hb he.symm hs.symm⟩
  intro h
  by_contra hr
  rcases lt_or_eq_of_le (Nat.le_of_not_gt hr) with hr | hr
  · exact (lt_asymm h (incoming_mates_reverse_key_order g hg bits hb hc he hs hr)).elim
  · have heq:=(List.idxOf_inj ((mem_backEvents g bits b).mpr hb) ((mem_backEvents g bits c).mpr hc)).mp hr
    subst c
    exact (lt_irrefl _ h).elim

end PlanarHom.PlanarityLRDirect
