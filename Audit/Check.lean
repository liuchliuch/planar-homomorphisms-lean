import Audit.Contracts
import Audit.Solutions
import Lean.Meta
import Lean.Util.CollectAxioms

/-! In-process statement and dependency-axiom checks for trusted local sources.
This is not the official sandboxed comparator or independent kernel replay. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let targets := #[
    (`PlanarHomAudit.Contracts.theorem11, `PlanarHomAudit.Solutions.theorem11),
    (`PlanarHomAudit.Contracts.theorem13, `PlanarHomAudit.Solutions.theorem13),
    (`PlanarHomAudit.Contracts.corollary122_rectangular,
      `PlanarHomAudit.Solutions.corollary122_rectangular)]
  for (statement, solution) in targets do
    let some (.defnInfo spec) := env.find? statement
      | throwError m!"Missing proposition definition: {statement}"
    let some (.thmInfo proof) := env.find? solution
      | throwError m!"Missing proved theorem: {solution}"
    let equal ← liftTermElabM <| Meta.isDefEq spec.value proof.type
    unless equal do
      throwError m!"Statement mismatch: {solution} against {statement}"
    let (_, dependencies) := ((Lean.CollectAxioms.collect solution).run env).run {}
    for ax in dependencies.axioms do
      unless allowed.contains ax do
        throwError m!"Unexpected axiom {ax} in {solution}"
    let extraPremise := Expr.forallE `extra (mkConst `True) spec.value BinderInfo.default
    let acceptsExtra ← liftTermElabM <| Meta.isDefEq extraPremise proof.type
    if acceptsExtra then
      throwError m!"Negative control accepted an extra premise for {solution}"
    logInfo m!"EXTRA_PREMISE_REJECTED {solution}"
    logInfo m!"CONTRACT_PASS {solution} == {statement}"
    logInfo m!"CONTRACT_AXIOMS {solution}: {dependencies.axioms}"
