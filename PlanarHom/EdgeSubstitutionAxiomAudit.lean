import PlanarHom.EdgeSubstitutionRegressions
import Lean.Util.CollectAxioms
open Lean Elab Command

#print axioms PlanarHom.EdgeSubstitution.fp_substitute
#print axioms PlanarHom.EdgeSubstitution.substitute_raw_outputs
#print axioms PlanarHom.FixedGadgetNetwork.factor_attachTemplate
#print axioms PlanarHom.FixedGadgetNetwork.sum_factor_compile
#print axioms PlanarHom.EdgeSubstitution.evaluate_substitute

-- Actual module-origin selection includes private/generated declarations and
-- every transitively imported project declaration, not a name-prefix sample.
run_cmd do
  let env ← getEnv
  let mut theoremCount := 0
  let mut declarationCount := 0
  let mut auditState : Lean.CollectAxioms.State := {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for moduleName in env.header.moduleNames do
    if (`PlanarHom).isPrefixOf moduleName || moduleName == `PlanarHom.EdgeSubstitutionRegressions then
      logInfo m!"AUDITED_MODULE {moduleName}"
  for (name, _) in env.constants.toList do
    let selectedOrigin := match env.getModuleIdxFor? name with
      | some idx =>
        let moduleName := env.header.moduleNames[idx.toNat]!
        (`PlanarHom).isPrefixOf moduleName || moduleName == `PlanarHom.EdgeSubstitutionRegressions
      | none => false
    if selectedOrigin then
      let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run auditState
      auditState := nextState
      logInfo m!"CHECKED {name}"
      for ax in auditState.axioms do
        unless allowed.contains ax do
          throwError m!"Unexpected axiom {ax}, discovered while visiting {name}"
      declarationCount := declarationCount + 1
      if Lean.wasOriginallyTheorem env name then theoremCount := theoremCount + 1
  logInfo m!"AXIOM_UNION={auditState.axioms}"
  logInfo m!"THEOREM_COUNT={theoremCount}"
  logInfo m!"DECLARATION_COUNT={declarationCount}"
  logInfo "AXIOM_AUDIT_PASS: every imported project and regression declaration; only propext, Classical.choice, Quot.sound"
