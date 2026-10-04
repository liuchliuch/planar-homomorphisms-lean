import PlanarHom.FktClippingRegressions
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Module-origin selection covers all project declarations, irrespective of public,
-- helper or private namespace. This includes reimplemented helper namespaces.
run_cmd do
  let env ← getEnv
  let mut theoremCount := 0
  let mut declarationCount := 0
  let mut auditState : Lean.CollectAxioms.State := {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for moduleName in env.header.moduleNames do
    if (`PlanarHom).isPrefixOf moduleName then logInfo m!"AUDITED_MODULE {moduleName}"
  for (name, _) in env.constants.toList do
    let projectOrigin := match env.getModuleIdxFor? name with
      | some idx => (`PlanarHom).isPrefixOf env.header.moduleNames[idx.toNat]! ||
          env.header.moduleNames[idx.toNat]! == `PlanarHom.FktClippingRegressions
      | none => false
    if projectOrigin then
      let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run auditState
      auditState := nextState
      logInfo m!"CHECKED {name}"
      for ax in auditState.axioms do
        unless allowed.contains ax do
          throwError m!"Unexpected axiom {ax}, discovered while visiting {name}"
      declarationCount := declarationCount + 1
      if Lean.wasOriginallyTheorem env name then theoremCount := theoremCount + 1
  logInfo m!"AXIOM_UNION={auditState.axioms}"
  logInfo m!"PROJECT_THEOREM_COUNT={theoremCount}"
  logInfo m!"PROJECT_DECLARATION_COUNT={declarationCount}"
  logInfo "AXIOM_AUDIT_PASS: every imported project declaration; only propext, Classical.choice, Quot.sound"
