import PlanarHom.PlanarityLRAlignment
import PlanarHom.PlanarityLRReturnFacts
import PlanarHom.PlanarityLRRawRegressions

namespace PlanarHom.PlanarityLRConstraintBlocks.StructureRegression

example : (decideAlignedBlocks ([([0,1],[2,3])],[(0,1)])).1 = true := by decide
example : (decideAlignedBlocks ([([0,1],[2,3])],[(0,2)])).1 = false := by decide
example : (decideAlignedBlocks ([([0,1],[2,3])],[(4,5)])).1 = true := by decide

theorem same_side_safe : AlignmentSafe [([0,1],[2,3])] [(0,1)] := by
  intro p hp _
  have hp' : p = (0,1) := by simpa using hp
  subst p
  exact ⟨([0,1],[2,3]),by simp,Or.inl ⟨by simp,by simp⟩⟩

theorem safe_alignment_preserves_existence :
    (∃ side, LRPartition side [([0,1],[2,3])] ∧ Aligned side [(0,1)]) ↔
      ∃ side, LRPartition side [([0,1],[2,3])] := exists_aligned_iff _ _ same_side_safe

end PlanarHom.PlanarityLRConstraintBlocks.StructureRegression

namespace PlanarHom.PlanarityLRRawConstraints.StructureRegression
open Complexity PlanarityDepthFirstSearch

/-- Actual back-edge ancestry has no additional DFS-correctness hypothesis. -/
example (g : MixedCode) (hg : g.Valid 1 0) {e : ℕ} (he : isBack g e = true) :
    target g e ∈ ancestors g (source g e) := back_target_ancestor g hg he

/-- Actual computed tree edges connect consecutive depths. -/
example (g : MixedCode) (hg : g.Valid 1 0) {e : ℕ} (he : isTree g e = true) :
    height g (target g e) = height g (source g e)+1 := tree_height_succ g hg he

/-- The computed lowpoint is bounded by every actual returned target. -/
example (g : MixedCode) (e b : ℕ) (hb : b ∈ returns g e) :
    lowpoint g e ≤ targetHeight g b := lowpoint_le_return g e hb

end PlanarHom.PlanarityLRRawConstraints.StructureRegression
