import PlanarHom.PlanarityLRConstraints
import PlanarHom.PlanarityLRStructureRegressions

/-! NEW tests of graph-specific alignment and literal output bits. -/
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace PlanarHom.PlanarityLRConstraints.Regression
open Complexity PlanarityLRRawConstraints PlanarityLRRawConstraints.Regression PlanarityLRConstraintBlocks

example : (decideAligned (completeGraph 0)).2 = [] := by decide
example : (decideAligned (completeGraph 3)).1 = true := by decide
example : (decideAligned parallelLoops).1 = true := by decide
example : (decideAligned parallelLoops).2.length = 4 := by decide

/-- No alignment certificate is added to the raw-code input. -/
example (g : MixedCode) (hg : g.Valid 1 0) :
    AlignmentSafe (forkBlocks g) (alignmentPairs g) := alignmentPairs_safe g hg

example (g : MixedCode) (hg : g.Valid 1 0) :
    (solveAlignedLR g).1 = (solveLR g).1 := solveAlignedLR_flag g hg

example (g : MixedCode) (h : (decideAligned g).1 = true) :
    LRCondition g (bitSide (decideAligned g).2) ∧
      Aligned (bitSide (decideAligned g).2) (alignmentPairs g) := decideAligned_sound g h

#eval decideAligned (completeGraph 4)
#eval (decideAligned (completeGraph 5)).1
#eval (decideAligned (completeBipartite 3 3)).1

end PlanarHom.PlanarityLRConstraints.Regression
