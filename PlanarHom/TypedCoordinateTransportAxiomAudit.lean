/- NEW audit harness for reconstructed coordinate transport. -/
import PlanarHom.TypedCoordinateTransportRegressions
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Includes all local transitive dependencies and private generated declarations.
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
      if Lean.wasOriginallyTheorem env name then
        theoremCount := theoremCount + 1
  logInfo m!"AXIOM_UNION={auditState.axioms}"
  logInfo m!"PROJECT_THEOREM_COUNT={theoremCount}"
  logInfo m!"PROJECT_DECLARATION_COUNT={declarationCount}"
  logInfo "RECONSTRUCTED_TYPED_COORDINATE_TRANSPORT_AXIOM_AUDIT_PASS: only propext, Classical.choice, Quot.sound"
