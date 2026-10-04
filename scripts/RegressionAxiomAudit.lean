-- PLGH_REGRESSION_IMPORT
import Lean.Util.CollectAxioms

/-! Template instantiated once per regression suite by verify_current.py.
Historical tests have overlapping global names and must remain isolated.
The production aggregate has its separate complete module-origin audit. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut theoremCount := 0
  let mut declarationCount := 0
  let mut auditState : Lean.CollectAxioms.State := {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for moduleName in env.header.moduleNames do
    if (`scripts).isPrefixOf moduleName then logInfo m!"AUDITED_MODULE {moduleName}"
  for (name, _) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if (`scripts).isPrefixOf origin then
      let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run auditState
      auditState := nextState
      logInfo m!"CHECKED_ORIGIN {origin} {name}"
      for ax in auditState.axioms do
        unless allowed.contains ax do
          throwError m!"Unexpected axiom {ax}, discovered while visiting {name}"
      declarationCount := declarationCount + 1
      if Lean.wasOriginallyTheorem env name then theoremCount := theoremCount + 1
  logInfo m!"AXIOM_UNION={auditState.axioms}"
  logInfo m!"REGRESSION_THEOREM_COUNT={theoremCount}"
  logInfo m!"REGRESSION_DECLARATION_COUNT={declarationCount}"
  logInfo "REGRESSION_AXIOM_AUDIT_PASS: all imported regression declarations; only propext, Classical.choice, Quot.sound"
