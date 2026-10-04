import PlanarHom.PlanarityLRContourPermutation

/-! NEW exact DFS subtree cuts. Every selected parent edge is the unique
selected edge entering its child subtree; this drives contour-cycle merging. -/
namespace PlanarHom.PlanarityLRRealization
open Complexity PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

theorem tree_child_not_desc_source (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isTree g e=true) : ¬Desc g (target g e) (source g e) := by
  intro hd
  have hs := (source_target_valid g hg (of_decide_eq_true he).1).1
  have hh := desc_height_le g hs hd
  have hstep := tree_height_succ g hg he
  omega

theorem tree_subtree_forward (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {w f : ℕ} (hf : isTree g f=true) (h : Desc g w (source g f)) : Desc g w (target g f) :=
  desc_trans g (source_target_valid g hg (of_decide_eq_true hf).1).2 h
    (Or.inr (tree_source_ancestor g hg hf))

/-- No selected DFS edge other than e enters the descendants of target e. -/
theorem tree_subtree_unique_entry (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e f : ℕ} (he : isTree g e=true) (hf : isTree g f=true)
    (hin : Desc g (target g e) (target g f)) (hout : ¬Desc g (target g e) (source g f)) : f=e := by
  rcases hin with heq | ha
  · exact tree_target_injective g hg hf he heq.symm
  · have hp := tree_source_parent g hg hf
    have hv := (source_target_valid g hg (of_decide_eq_true hf).1).2
    rw [ancestors_parent g hv hp.2.2,← hp.1] at ha
    exact False.elim (hout (by simpa only [List.mem_cons,Desc] using ha))

end PlanarHom.PlanarityLRRealization
