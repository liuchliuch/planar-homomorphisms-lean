import PlanarHom.PlanarityLRReturnEventOrder

/-! NEW order of every back edge leaving a computed vertex subtree, including
returns to its parent. This is the complete boundary-return invariant. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints
open PlanarityLRConstraintBlocks

def EscapesSubtree (g : MixedCode) (v b : ℕ) : Prop :=
  isBack g b=true ∧ Desc g v (source g b) ∧ targetHeight g b < height g v

 theorem escaping_events_ordered_fork (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {w b c : ℕ} (hb : EscapesSubtree g w b) (hc : EscapesSubtree g w c)
    (hrank : (backEvents g bits).idxOf b < (backEvents g bits).idxOf c) :
    ∃ v e f, v < g.vertices ∧ 0 < height g v ∧ e ∈ outgoing g v ∧ f ∈ outgoing g v ∧ f≠e ∧
      (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f ∧
      b ∈ returns g e ∧ c ∈ returns g f := by
  have hsb := (source_target_valid g hg (of_decide_eq_true hb.1).1).1
  have hsc := (source_target_valid g hg (of_decide_eq_true hc.1).1).1
  have hw := desc_valid g hsb hb.2.1
  have hr : componentRoot g (source g b)=componentRoot g (source g c) :=
    (componentRoot_eq_of_desc g hsb hb.2.1).symm.trans (componentRoot_eq_of_desc g hsc hc.2.1)
  obtain ⟨v,hv,hvb,hvc,hmax⟩ := exists_deepest_common_ancestor g hsb hsc hr
  have hvdepth := hmax w hw hb.2.1 hc.2.1
  obtain ⟨e,he⟩ := exists_back_branch g hg hb.1 hvb
  obtain ⟨f,hf⟩ := exists_back_branch g hg hc.1 hvc
  have hbc : b≠c := by intro h; rw [h] at hrank; omega
  have hef := he.ne_of_deepest hg hf hb.1 hc.1 hbc hmax
  have hord := (he.event_rank_lt_iff hg bits hf hb.1 hc.1 hef).mp hrank
  refine ⟨v,e,f,hv,by have := hb.2.2; omega,he.outgoing,hf.outgoing,hef.symm,hord,?_,?_⟩
  · exact he.return_mem hb.1 (by have := hb.2.2; omega)
  · exact hf.return_mem hc.1 (by have := hc.2.2; omega)

 theorem escaping_event_rank_semantics (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    {v b c : ℕ} (hb : EscapesSubtree g v b) (hc : EscapesSubtree g v c)
    (hrank : (backEvents g bits).idxOf b < (backEvents g bits).idxOf c) : ReturnOrder g bits b c := by
  obtain ⟨v,e,f,hv,hh,he,hf,hne,hord,hbe,hcf⟩ := escaping_events_ordered_fork g hg bits hb hc hrank
  cases hbs : bitSide bits b with
  | false =>
      cases hcs : bitSide bits c with
      | false => exact Or.inr (Or.inr ⟨hbs,hcs,left_return_le_of_after g bits hLR hv hh he hf hne hord hbe hcf hcs⟩)
      | true => exact Or.inl ⟨hbs,hcs⟩
  | true =>
      cases hcs : bitSide bits c with
      | false => exact False.elim (no_right_before_left_returns g hg bits hLR halign hv hh he hf hne hord hbe hcf hbs hcs)
      | true => exact Or.inr (Or.inl ⟨hbs,hcs,right_return_le_of_before g bits hLR hv hh he hf hne hord hbe hcf hbs⟩)

/-- All exterior return events of a vertex subtree, in the actual DFS event order. -/
def escapeEvents (g : MixedCode) (bits : List Bool) (v : ℕ) : List ℕ :=
  (backEvents g bits).filter (fun b => ancestor g v (source g b) && decide (targetHeight g b < height g v))

@[simp] theorem mem_escapeEvents (g : MixedCode) (bits : List Bool) (v b : ℕ) :
    b ∈ escapeEvents g bits v ↔ EscapesSubtree g v b := by
  simp only [escapeEvents,List.mem_filter,mem_backEvents,Bool.and_eq_true,ancestor,decide_eq_true_eq,EscapesSubtree,Desc]

 theorem escapeEvents_ordered (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    (v : ℕ) : (escapeEvents g bits v).Pairwise (ReturnOrder g bits) := by
  have hranks : (backEvents g bits).Pairwise (fun b c => (backEvents g bits).idxOf b < (backEvents g bits).idxOf c) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.idxOf_getElem (backEvents_nodup g bits)] using hij
  apply (hranks.filter (fun b => ancestor g v (source g b) && decide (targetHeight g b < height g v))).imp_of_mem
  intro b c hb hc hbc
  exact escaping_event_rank_semantics g hg bits hLR halign
    ((mem_escapeEvents g bits v b).mp hb) ((mem_escapeEvents g bits v c).mp hc) hbc

 theorem computed_escapeEvents_ordered (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hflag : (decideAligned g).1=true) (v : ℕ) :
    (escapeEvents g (decideAligned g).2 v).Pairwise (ReturnOrder g (decideAligned g).2) := by
  have h := decideAligned_sound g hflag
  exact escapeEvents_ordered g hg (decideAligned g).2 h.1 h.2 v

end PlanarHom.PlanarityLRDirect
