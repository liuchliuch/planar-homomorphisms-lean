import PlanarHom.PlanarityLRGeneralBranchOrder
import PlanarHom.PlanarityLRAlignedForkOrder

/-! NEW global order of the actual DFS return-event lists: left returns first,
with descending target heights, then right returns with ascending target heights. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints
open PlanarityLRConstraintBlocks

 theorem tree_returns_ordered_fork (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {t b c : ℕ} (ht : isTree g t=true)
    (hb : b ∈ returns g t) (hc : c ∈ returns g t)
    (hrank : (backEvents g bits).idxOf b < (backEvents g bits).idxOf c) :
    ∃ v e f, v < g.vertices ∧ 0 < height g v ∧ e ∈ outgoing g v ∧ f ∈ outgoing g v ∧ f≠e ∧
      (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f ∧
      b ∈ returns g e ∧ c ∈ returns g f := by
  have hbR := (returns_tree_iff g ht b).mp hb
  have hcR := (returns_tree_iff g ht c).mp hc
  have hsb := (source_target_valid g hg (of_decide_eq_true hbR.1).1).1
  have hsc := (source_target_valid g hg (of_decide_eq_true hcR.1).1).1
  have htval := (source_target_valid g hg (of_decide_eq_true ht).1).2
  have hr : componentRoot g (source g b)=componentRoot g (source g c) :=
    (componentRoot_eq_of_desc g hsb hbR.2.1).symm.trans (componentRoot_eq_of_desc g hsc hcR.2.1)
  obtain ⟨v,hv,hvb,hvc,hmax⟩ := exists_deepest_common_ancestor g hsb hsc hr
  have hvdepth := hmax (target g t) htval hbR.2.1 hcR.2.1
  have hstep := tree_height_succ g hg ht
  obtain ⟨e,he⟩ := exists_back_branch g hg hbR.1 hvb
  obtain ⟨f,hf⟩ := exists_back_branch g hg hcR.1 hvc
  have hbc : b≠c := by intro h; rw [h] at hrank; omega
  have hef := he.ne_of_deepest hg hf hbR.1 hcR.1 hbc hmax
  have hord := (he.event_rank_lt_iff hg bits hf hbR.1 hcR.1 hef).mp hrank
  refine ⟨v,e,f,hv,by omega,he.outgoing,hf.outgoing,hef.symm,hord,?_,?_⟩
  · exact he.return_mem hbR.1 (by omega)
  · exact hf.return_mem hcR.1 (by omega)

/-- The complete order invariant consumed by the embedding construction. -/
def ReturnOrder (g : MixedCode) (bits : List Bool) (b c : ℕ) : Prop :=
  (bitSide bits b=false ∧ bitSide bits c=true) ∨
    (bitSide bits b=true ∧ bitSide bits c=true ∧ targetHeight g b≤targetHeight g c) ∨
    (bitSide bits b=false ∧ bitSide bits c=false ∧ targetHeight g c≤targetHeight g b)

 theorem tree_return_rank_semantics (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    {t b c : ℕ} (ht : isTree g t=true) (hb : b ∈ returns g t) (hc : c ∈ returns g t)
    (hrank : (backEvents g bits).idxOf b < (backEvents g bits).idxOf c) : ReturnOrder g bits b c := by
  obtain ⟨v,e,f,hv,hh,he,hf,hne,hord,hbe,hcf⟩ := tree_returns_ordered_fork g hg bits ht hb hc hrank
  cases hbs : bitSide bits b with
  | false =>
      cases hcs : bitSide bits c with
      | false => exact Or.inr (Or.inr ⟨hbs,hcs,left_return_le_of_after g bits hLR hv hh he hf hne hord hbe hcf hcs⟩)
      | true => exact Or.inl ⟨hbs,hcs⟩
  | true =>
      cases hcs : bitSide bits c with
      | false => exact False.elim (no_right_before_left_returns g hg bits hLR halign hv hh he hf hne hord hbe hcf hbs hcs)
      | true => exact Or.inr (Or.inl ⟨hbs,hcs,right_return_le_of_before g bits hLR hv hh he hf hne hord hbe hcf hbs⟩)

/-- Actual event sorting, restricted to a tree edge's literal returns. -/
def returnEvents (g : MixedCode) (bits : List Bool) (t : ℕ) : List ℕ :=
  (backEvents g bits).filter (fun b => decide (b ∈ returns g t))

 theorem returnEvents_ordered (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    {t : ℕ} (ht : isTree g t=true) : (returnEvents g bits t).Pairwise (ReturnOrder g bits) := by
  have hranks : (backEvents g bits).Pairwise (fun b c => (backEvents g bits).idxOf b < (backEvents g bits).idxOf c) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.idxOf_getElem (backEvents_nodup g bits)] using hij
  apply (hranks.filter (fun b => decide (b ∈ returns g t))).imp_of_mem
  intro b c hb hc hbc
  exact tree_return_rank_semantics g hg bits hLR halign ht
    (of_decide_eq_true (List.mem_filter.mp hb).2) (of_decide_eq_true (List.mem_filter.mp hc).2) hbc

 theorem computed_returnEvents_ordered (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hflag : (decideAligned g).1=true) {t : ℕ} (ht : isTree g t=true) :
    (returnEvents g (decideAligned g).2 t).Pairwise (ReturnOrder g (decideAligned g).2) := by
  have h := decideAligned_sound g hflag
  exact returnEvents_ordered g hg (decideAligned g).2 h.1 h.2 ht

end PlanarHom.PlanarityLRDirect
