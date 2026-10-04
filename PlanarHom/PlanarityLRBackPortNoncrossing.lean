import PlanarHom.PlanarityLREscapeEventOrder
import PlanarHom.PlanarityLRPortBranches
import PlanarHom.PlanarityLRIncomingMateOrder
import PlanarHom.OrderedPortIntervals

/-! NEW global paired-back-port noninterleaving in the exact computed contour
key order. Every case uses actual DFS forks, LR alignment and literal mate rows. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints PlanarityRotationCode
open PlanarityLRConstraintBlocks

 theorem back_port_key_noncrossing_of_rank (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true)
    (hr : componentRoot g (source g b)=componentRoot g (source g c))
    (hrank : (backEvents g bits).idxOf b < (backEvents g bits).idxOf c) :
    PortNoncrossing (contourKey g bits (outward g b)) (contourKey g bits (reverse (outward g b)))
      (contourKey g bits (outward g c)) (contourKey g bits (reverse (outward g c))) := by
  have hbval := (of_decide_eq_true hb).1
  have hcval := (of_decide_eq_true hc).1
  have hsb := (source_target_valid g hg hbval).1
  have hsc := (source_target_valid g hg hcval).1
  have htb := (source_target_valid g hg hbval).2
  have htc := (source_target_valid g hg hcval).2
  have hbc : b≠c := by intro h; rw [h] at hrank; omega
  obtain ⟨v,e,f,hv,hvb,hvc,H,K,hef⟩ := exists_back_edge_fork g hg hb hc hbc hr
  have hord := (H.event_rank_lt_iff hg bits K hb hc hef).mp hrank
  have heO := (mem_orderedOutgoing g bits v e).mpr H.outgoing
  have hfO := (mem_orderedOutgoing g bits v f).mpr K.outgoing
  have hsep (a d : Dart) (ha : a.1 < g.edges.length) (hd : d.1 < g.edges.length)
      (heA : InExpandedBranch g bits e a) (hfD : InExpandedBranch g bits f d) :
      contourKey g bits a < contourKey g bits d :=
    branch_block_key_separation g hg bits heO hfO hord ha hd heA hfD
  have hObOc := hsep (outward g b) (outward g c) hbval hcval (H.outward_in_expanded bits) (K.outward_in_expanded bits)
  have htgtB (hge : height g v≤targetHeight g b) : Desc g v (target g b) :=
    desc_of_height_le g hsb hvb (Or.inr (back_target_ancestor g hg hb)) hge
  have htgtC (hge : height g v≤targetHeight g c) : Desc g v (target g c) :=
    desc_of_height_le g hsc hvc (Or.inr (back_target_ancestor g hg hc)) hge
  by_cases hBG : height g v≤targetHeight g b
  · have hMb := H.inward_in_expanded_of_target_ge hg bits hb hBG
    have hMbOc := hsep (reverse (outward g b)) (outward g c) hbval hcval hMb (K.outward_in_expanded bits)
    by_cases hCG : height g v≤targetHeight g c
    · have hMc := K.inward_in_expanded_of_target_ge hg bits hc hCG
      exact portNoncrossing_separated hObOc
        (hsep (outward g b) (reverse (outward g c)) hbval hcval (H.outward_in_expanded bits) hMc) hMbOc
        (hsep (reverse (outward g b)) (reverse (outward g c)) hbval hcval hMb hMc)
    · have hchild := branchChild_desc_of_target_lt g hg hc hvc (lt_of_not_ge hCG)
      have hdO : Desc g (branchChild g c) (host g (outward g b)) := by
        rw [host_outward]; exact desc_trans g hsb hchild hvb
      have hdM : Desc g (branchChild g c) (host g (reverse (outward g b))) := by
        rw [host_reverse_outward]; exact desc_trans g htb hchild (htgtB hBG)
      cases hcs : bitSide bits c with
      | false =>
          have hMcOb := incoming_false_before_subtree g hg bits hc hcs hbval hdO
          have hMcMb := incoming_false_before_subtree g hg bits hc hcs hbval hdM
          exact (portNoncrossing_inside hMcOb hMcMb hObOc hMbOc).swap_right
      | true =>
          have hObMc := incoming_true_after_subtree g hg bits hc hcs hbval hdO
          have hMbMc := incoming_true_after_subtree g hg bits hc hcs hbval hdM
          exact portNoncrossing_separated hObOc hObMc hMbOc hMbMc
  · by_cases hCG : height g v≤targetHeight g c
    · have hMc := K.inward_in_expanded_of_target_ge hg bits hc hCG
      have hObMc := hsep (outward g b) (reverse (outward g c)) hbval hcval (H.outward_in_expanded bits) hMc
      have hchild := branchChild_desc_of_target_lt g hg hb hvb (lt_of_not_ge hBG)
      have hdO : Desc g (branchChild g b) (host g (outward g c)) := by
        rw [host_outward]; exact desc_trans g hsc hchild hvc
      have hdM : Desc g (branchChild g b) (host g (reverse (outward g c))) := by
        rw [host_reverse_outward]; exact desc_trans g htc hchild (htgtC hCG)
      cases hbs : bitSide bits b with
      | false =>
          have hMbOc := incoming_false_before_subtree g hg bits hb hbs hcval hdO
          have hMbMc := incoming_false_before_subtree g hg bits hb hbs hcval hdM
          exact portNoncrossing_separated hObOc hObMc hMbOc hMbMc
      | true =>
          have hOcMb := incoming_true_after_subtree g hg bits hb hbs hcval hdO
          have hMcMb := incoming_true_after_subtree g hg bits hb hbs hcval hdM
          exact (portNoncrossing_inside hObOc hObMc hOcMb hMcMb).symm
    · have hBL : targetHeight g b < height g v := lt_of_not_ge hBG
      have hCL : targetHeight g c < height g v := lt_of_not_ge hCG
      have hret := escaping_event_rank_semantics g hg bits hLR halign
        (show EscapesSubtree g v b from ⟨hb,hvb,hBL⟩) (show EscapesSubtree g v c from ⟨hc,hvc,hCL⟩) hrank
      have hdB := (branchChild_spec g hg hb).2.1
      have hdC := (branchChild_spec g hg hc).2.1
      have hleftB (hbs : bitSide bits b=false) : contourKey g bits (reverse (outward g b)) < contourKey g bits (outward g b) :=
        incoming_false_before_subtree g hg bits hb hbs hbval (by simpa only [host_outward] using hdB)
      have hrightB (hbs : bitSide bits b=true) : contourKey g bits (outward g b) < contourKey g bits (reverse (outward g b)) :=
        incoming_true_after_subtree g hg bits hb hbs hbval (by simpa only [host_outward] using hdB)
      have hleftC (hcs : bitSide bits c=false) : contourKey g bits (reverse (outward g c)) < contourKey g bits (outward g c) :=
        incoming_false_before_subtree g hg bits hc hcs hcval (by simpa only [host_outward] using hdC)
      have hrightC (hcs : bitSide bits c=true) : contourKey g bits (outward g c) < contourKey g bits (reverse (outward g c)) :=
        incoming_true_after_subtree g hg bits hc hcs hcval (by simpa only [host_outward] using hdC)
      have hmates (hs : bitSide bits b=bitSide bits c) (hheight : targetHeight g b=targetHeight g c) :
          contourKey g bits (reverse (outward g c)) < contourKey g bits (reverse (outward g b)) := by
        have htvB := target_desc_of_target_lt g hg hb hvb hBL
        have htvC := target_desc_of_target_lt g hg hc hvc hCL
        have htEq := desc_eq_of_equal_height g hv htvB htvC hheight
        have hbranch := branchEdge_eq_of_common_target g hg hb hc hvb hvc htEq hBL
        exact incoming_mates_reverse_key_order g hg bits hb hc hbranch hs hrank
      rcases hret with ⟨hbs,hcs⟩ | ⟨hbs,hcs,hle⟩ | ⟨hbs,hcs,hle⟩
      · have hMbOb := hleftB hbs
        have hOcMc := hrightC hcs
        exact portNoncrossing_separated hObOc (hObOc.trans hOcMc) (hMbOb.trans hObOc) ((hMbOb.trans hObOc).trans hOcMc)
      · have hMcMb : contourKey g bits (reverse (outward g c)) < contourKey g bits (reverse (outward g b)) := by
          by_cases hEq : targetHeight g b=targetHeight g c
          · exact hmates (hbs.trans hcs.symm) hEq
          · have hlt : targetHeight g b < targetHeight g c := by omega
            have hchildV := branchChild_desc_of_target_lt g hg hb hvb hBL
            have htC := target_desc_of_target_lt g hg hc hvc hCL
            have hhchild := (branchChild_spec g hg hb).2.2
            have hd := desc_of_height_le g hv hchildV htC (by change height g (branchChild g b)≤targetHeight g c; omega)
            exact incoming_true_after_subtree g hg bits hb hbs hcval (by simpa only [host_reverse_outward] using hd)
        have hOcMc := hrightC hcs
        exact (portNoncrossing_inside hObOc (hObOc.trans hOcMc) (hOcMc.trans hMcMb) hMcMb).symm
      · have hMcMb : contourKey g bits (reverse (outward g c)) < contourKey g bits (reverse (outward g b)) := by
          by_cases hEq : targetHeight g b=targetHeight g c
          · exact hmates (hbs.trans hcs.symm) hEq
          · have hlt : targetHeight g c < targetHeight g b := by omega
            have hchildV := branchChild_desc_of_target_lt g hg hc hvc hCL
            have htB := target_desc_of_target_lt g hg hb hvb hBL
            have hhchild := (branchChild_spec g hg hc).2.2
            have hd := desc_of_height_le g hv hchildV htB (by change height g (branchChild g c)≤targetHeight g b; omega)
            exact incoming_false_before_subtree g hg bits hc hcs hbval (by simpa only [host_reverse_outward] using hd)
        have hMbOb := hleftB hbs
        exact (portNoncrossing_inside (hMcMb.trans hMbOb) hMcMb hObOc (hMbOb.trans hObOc)).swap_right

 theorem back_port_key_noncrossing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true) (hne : b≠c)
    (hr : componentRoot g (source g b)=componentRoot g (source g c)) :
    PortNoncrossing (contourKey g bits (outward g b)) (contourKey g bits (reverse (outward g b)))
      (contourKey g bits (outward g c)) (contourKey g bits (reverse (outward g c))) := by
  have hidx : (backEvents g bits).idxOf b≠(backEvents g bits).idxOf c := by
    intro h
    exact hne ((List.idxOf_inj ((mem_backEvents g bits b).mpr hb) ((mem_backEvents g bits c).mpr hc)).mp h)
  rcases lt_or_gt_of_ne hidx with h | h
  · exact back_port_key_noncrossing_of_rank g hg bits hLR halign hb hc hr h
  · exact (back_port_key_noncrossing_of_rank g hg bits hLR halign hc hb hr.symm h).symm

/-- The actual raw-input LR output has noninterleaving back-port pairs whenever
its own computed flag accepts. -/
theorem computed_back_port_key_noncrossing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hflag : (decideAligned g).1=true) {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true) (hne : b≠c)
    (hr : componentRoot g (source g b)=componentRoot g (source g c)) :
    PortNoncrossing (contourKey g (decideAligned g).2 (outward g b))
      (contourKey g (decideAligned g).2 (reverse (outward g b)))
      (contourKey g (decideAligned g).2 (outward g c))
      (contourKey g (decideAligned g).2 (reverse (outward g c))) := by
  have hs := decideAligned_sound g hflag
  exact back_port_key_noncrossing g hg (decideAligned g).2 hs.1 hs.2 hb hc hne hr

end PlanarHom.PlanarityLRDirect
