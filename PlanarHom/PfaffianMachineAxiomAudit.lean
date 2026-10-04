import PlanarHom.OccurrencePfaffianEvaluationMachines
import PlanarHom.PfaffianMachineRegressions
import Lean.Util.CollectAxioms

/-! NEW broad axiom audit, including all reachable PlanarHom declarations and
private/generated declarations. -/
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut declarationCount := 0
  let mut theoremCount := 0
  let mut auditState : Lean.CollectAxioms.State := {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    if (`PlanarHom).isPrefixOf name || (`ReimplementedPfaffianMachine).isPrefixOf name ||
        name.toString.startsWith "_private.PlanarHom." ||
        name.toString.startsWith "_private.ReimplementedPfaffianMachine." then
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
  logInfo "PFAFFIAN_MACHINE_AXIOM_AUDIT_PASS"

#print axioms PlanarHom.PfaffianList.fp_evaluateGrid
#print axioms PlanarHom.PfaffianList.exists_iteration_state_encoding_polynomial
#print axioms PlanarHom.PfaffianList.evaluateGrid_eq_elimination

#print axioms PlanarHom.PfaffianList.certified_evaluateGrid
#print axioms PlanarHom.PfaffianList.evaluateGrid_matrixRows
#print axioms PlanarHom.PfaffianList.matchingSum_eq_referenceSign_mul_evaluateGrid
#print axioms PlanarHom.OccurrenceSkewCode.fp_evaluate
#print axioms PlanarHom.OccurrenceSkewCode.evaluate_eq_pairingPfaffian
#print axioms PlanarHom.OccurrenceSkewCode.calibrated_evaluation
