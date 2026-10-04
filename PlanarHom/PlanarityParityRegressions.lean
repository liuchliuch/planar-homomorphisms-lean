import PlanarHom.PlanarityParityPolynomial

/-! NEW executable and kernel-checked parity-elimination regressions. -/
namespace PlanarHom.PlanarityParitySolver.Regression

example : computed [] = (true,[]) := by decide
example : (computed [(7,7,false)]).1 = true := by decide
example : (computed [(7,7,true)]).1 = false := by decide
example : (computed [(0,1,true),(0,1,true)]).1 = true := by decide
example : (computed [(0,1,true),(0,1,false)]).1 = false := by decide
example : (computed [(0,1,true),(1,2,true),(2,0,true)]).1 = false := by decide
example : (computed [(0,1,true),(1,2,true),(2,0,false)]).1 = true := by decide
example : (computed [(1000000,8000000,true),(8000000,3,false)]).1 = true := by decide

/-- Successful actual output, including sparse binary labels, satisfies all equations. -/
theorem sparse_assignment :
    Satisfies (lookup (computed [(1000000,8000000,true),(8000000,3,false)]).2)
      [(1000000,8000000,true),(8000000,3,false)] := computed_sound _ (by decide)

/-- Rejection proves inconsistency; it does not require an external failure witness. -/
theorem inconsistent_triangle :
    ¬∃ f, Satisfies f [(0,1,true),(1,2,true),(2,0,true)] := by
  rw [← computed_complete]
  decide

/-- The exact field-free encoded solver is genuinely FP on arbitrary dynamic lists. -/
example : Complexity.FP constraintCode.list (Complexity.BitEncoding.bool.prod assignmentCode) computed := fp_computed

#eval computed [(0,1,true),(1,2,true),(2,0,false)]
#eval computed [(0,1,true),(1,2,true),(2,0,true)]
#eval solveWithWork [(1000000,8000000,true),(8000000,3,false)]

end PlanarHom.PlanarityParitySolver.Regression
