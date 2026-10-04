import PlanarHom.HomogeneousSourceOrientationReduction
import PlanarHom.HomogeneousSourceOrientationFullRegressions
import PlanarHom.HomogeneousSourceOrientationConnected
import PlanarHom.HomogeneousSourceOrientationSemantics
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let targets := #[`PlanarHom.HomogeneousSourceOrientationSemantics,
    `PlanarHom.HomogeneousSourceOrientationMachines,
    `PlanarHom.HomogeneousSourceOrientationConnected,
    `PlanarHom.HomogeneousSourceOrientationComponents,
    `PlanarHom.HomogeneousSourceOrientationCrossing,
    `PlanarHom.HomogeneousSourceOrientationReduction,
    `PlanarHom.HomogeneousSourceOrientationFullRegressions]
  for target in targets do
    unless env.header.moduleNames.contains target do
      throwError m!"Missing required source module: {target}"
    logInfo m!"REQUIRED_MODULE_PRESENT {target}"
  let mut declarationCount := 0
  let mut auditState : Lean.CollectAxioms.State := {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let selectedOrigin := match env.getModuleIdxFor? name with
      | some idx => ((`PlanarHom).isPrefixOf env.header.moduleNames[idx.toNat]! || env.header.moduleNames[idx.toNat]! == `PlanarHom.HomogeneousSourceOrientationFullRegressions)
      | none => false
    if selectedOrigin then
      let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run auditState
      auditState := nextState
      for ax in auditState.axioms do
        unless allowed.contains ax do
          throwError m!"Unexpected axiom {ax}, discovered while visiting {name}"
      declarationCount := declarationCount + 1
  logInfo m!"AXIOM_UNION={auditState.axioms}"
  logInfo m!"DECLARATION_COUNT={declarationCount}"
  logInfo "AXIOM_AUDIT_PASS: all project-origin declarations including private/generated; only propext, Classical.choice, Quot.sound"

#print axioms PlanarHom.AlgebraicProductInterpolation.RealLanguage.homogeneousSourceOrientation
#print axioms PlanarHom.AlgebraicProductInterpolation.RealLanguage.homogeneousUnitSourceOrientation
#check PlanarHom.AlgebraicProductInterpolation.RealLanguage.homogeneousSourceOrientation
#check PlanarHom.AlgebraicProductInterpolation.RealLanguage.homogeneousUnitSourceOrientation
