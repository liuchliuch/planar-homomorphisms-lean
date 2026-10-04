import PlanarHom.PlanarityLRRealizationRotationSystem
import PlanarHom.PlanarityLRTreeInsertion
import PlanarHom.PlanarityLRNestingMachines
import PlanarHom.PlanarityLRAlignedRegressions

/-! NEW kernel-checked edge cases for occurrence rotation construction. -/
namespace PlanarHom.PlanarityLRDirect.Regression
open Complexity PlanarityRotationCode PlanarityLRConstraints
open PlanarityLRRawConstraints.Regression

example : rowNext [] (9,true) = (9,true) := by decide
example : rowNext [(0,true),(1,false)] (2,true) = (1,false) := by decide
example : rowNext [(0,true),(1,false)] (1,false) = (0,true) := by decide
example (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v < g.vertices) :
    (directRow g bits v).Perm (incidentRow g v) := directRow_perm_incident g hg bits hv

#eval (List.range 3).map (fun n => (List.range n).map (directRow (completeGraph n) []))
#eval treeInsertionOrder (completeGraph 3)
#eval (List.range 2).map (directRow parallelLoops (decideAligned parallelLoops).2)

end PlanarHom.PlanarityLRDirect.Regression
