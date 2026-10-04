import PlanarHom.PlanarityLRFaceRegressions
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
  logInfo "RECONSTRUCTED_PLANARITY_LR_FACE_AXIOM_AUDIT_PASS"
#check PlanarHom.PlanarityLRDirect.componentRoot_spec
#check PlanarHom.PlanarityLRDirect.typedComponentTreeOrder_rooted
#check PlanarHom.PlanarityLRDirect.exists_computedTree_chart
#print axioms PlanarHom.PlanarityLRDirect.exists_computedTree_chart

#check PlanarHom.PlanarityLRRealization.mem_orbit_iff_sameCycle
#check PlanarHom.PlanarityLRRealization.boundary_eq_period_walk
#check PlanarHom.PlanarityLRRealization.boundary_nodup
#check PlanarHom.PlanarityLRRealization.representative_boundaries_disjoint
#check PlanarHom.PlanarityLRRealization.all_boundaries_perm_allDarts
#print axioms PlanarHom.PlanarityLRRealization.all_boundaries_perm_allDarts
