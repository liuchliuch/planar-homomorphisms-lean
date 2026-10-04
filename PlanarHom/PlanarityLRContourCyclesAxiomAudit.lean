import PlanarHom.PlanarityLRContourAxiomAudit
import PlanarHom.PlanarityLRContourCycles
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarationCount := 0
  let mut theoremCount := 0
  let mut auditState : Lean.CollectAxioms.State := {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    if (`PlanarHom).isPrefixOf name || name.toString.startsWith "_private.PlanarHom." then
      let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run auditState
      auditState := nextState
      for ax in auditState.axioms do
        unless allowed.contains ax do
          throwError m!"Unexpected axiom {ax}, discovered while visiting {name}"
      declarationCount := declarationCount + 1
      if Lean.wasOriginallyTheorem env name then theoremCount := theoremCount + 1
  logInfo m!"AXIOM_UNION={auditState.axioms}"
  logInfo m!"PROJECT_THEOREM_COUNT={theoremCount}"
  logInfo m!"PROJECT_DECLARATION_COUNT={declarationCount}"
  logInfo "RECONSTRUCTED_PLANARITY_LR_CONTOUR_CYCLES_AXIOM_AUDIT_PASS"
#check PlanarHom.FinitePermutationCut.sameCycle_of_unique_exit
#check PlanarHom.PlanarityLRRealization.tree_subtree_unique_entry
#check PlanarHom.PlanarityLRRealization.dfsContourForRows_sameCycle_iff_componentRoot_eq
#check PlanarHom.PlanarityLRRealization.mem_dfsContourForRowsPortWord
#print axioms PlanarHom.PlanarityLRRealization.dfsContourForRows_sameCycle_iff_componentRoot_eq

open PlanarHom PlanarHom.Complexity PlanarHom.PlanarityLRDirect PlanarHom.PlanarityLRRawConstraints
open PlanarHom.PlanarityLRRawConstraints.Regression PlanarHom.PlanarityRotationCode
private def rawContour (g : MixedCode) (a : Dart) : Dart := directRotation g [] (if isTree g a.1 then reverse a else a)
#eval (List.range 6).map (fun n => (rawContour (completeGraph 3))^[n] (0,true))
#eval (List.range 2).map (fun n => (rawContour ⟨1,[(0,(0,0))],[]⟩)^[n] (0,true))
