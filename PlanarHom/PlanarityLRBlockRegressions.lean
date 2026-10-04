import PlanarHom.PlanarityLRConstraintBlocks

/-! NEW exact fork-block compilation regressions. -/
namespace PlanarHom.PlanarityLRConstraintBlocks.Regression

example : (decideBlocks []).1 = true := by decide
example : (decideBlocks [([],[])]).1 = true := by decide
example : (decideBlocks [([0,1],[])]).1 = true := by decide
example : (decideBlocks [([0,1],[2,3])]).1 = true := by decide
example : (decideBlocks [([0],[0])]).1 = false := by decide
example : (decideBlocks [([0],[1]),([1],[2]),([2],[0])]).1 = false := by decide
example : (decideBlocks [([0,0],[1,1])]).1 = true := by decide
example : (equations ([0,1],[2,3])).length = 12 := by decide

theorem repeated_label_inconsistent : ¬∃ f, LRPartition f [([0],[0])] := by
  rw [← decideBlocks_complete]
  decide

theorem actual_assignment :
    LRPartition (PlanarityParitySolver.lookup (decideBlocks [([0,1],[2,3])]).2) [([0,1],[2,3])] :=
  decideBlocks_sound _ (by decide)

example : Complexity.FP blockCode.list
    (Complexity.BitEncoding.bool.prod PlanarityParitySolver.assignmentCode) decideBlocks := fp_decideBlocks

#eval decideBlocks [([0,1],[2,3])]
#eval decideBlocks [([0],[1]),([1],[2]),([2],[0])]

end PlanarHom.PlanarityLRConstraintBlocks.Regression
