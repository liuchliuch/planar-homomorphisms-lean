import Audit.ReviewedStatements
import Audit.ReviewedSolutions
import Lean.Meta
import Lean.Util.CollectAxioms

/-! Full-type comparisons, including data-valued reductions and universe levels.
Local trusted-source checking only; no independent kernel or sandbox claim. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let targets := #[
    ("1.1", `PlanarHomAudit.ReviewedStatements.item_1_1_1, `PlanarHomAudit.ReviewedSolutions.item_1_1_1),
    ("1.3", `PlanarHomAudit.ReviewedStatements.item_1_3_1, `PlanarHomAudit.ReviewedSolutions.item_1_3_1),
    ("2.2", `PlanarHomAudit.ReviewedStatements.item_2_2_1, `PlanarHomAudit.ReviewedSolutions.item_2_2_1),
    ("2.2", `PlanarHomAudit.ReviewedStatements.item_2_2_2, `PlanarHomAudit.ReviewedSolutions.item_2_2_2),
    ("2.3", `PlanarHomAudit.ReviewedStatements.item_2_3_1, `PlanarHomAudit.ReviewedSolutions.item_2_3_1),
    ("2.4", `PlanarHomAudit.ReviewedStatements.item_2_4_1, `PlanarHomAudit.ReviewedSolutions.item_2_4_1),
    ("2.4", `PlanarHomAudit.ReviewedStatements.item_2_4_2, `PlanarHomAudit.ReviewedSolutions.item_2_4_2),
    ("2.5", `PlanarHomAudit.ReviewedStatements.item_2_5_1, `PlanarHomAudit.ReviewedSolutions.item_2_5_1),
    ("2.6", `PlanarHomAudit.ReviewedStatements.item_2_6_1, `PlanarHomAudit.ReviewedSolutions.item_2_6_1),
    ("3.1", `PlanarHomAudit.ReviewedStatements.item_3_1_1, `PlanarHomAudit.ReviewedSolutions.item_3_1_1),
    ("3.1", `PlanarHomAudit.ReviewedStatements.item_3_1_2, `PlanarHomAudit.ReviewedSolutions.item_3_1_2),
    ("3.1", `PlanarHomAudit.ReviewedStatements.item_3_1_3, `PlanarHomAudit.ReviewedSolutions.item_3_1_3),
    ("3.1", `PlanarHomAudit.ReviewedStatements.item_3_1_4, `PlanarHomAudit.ReviewedSolutions.item_3_1_4),
    ("3.2", `PlanarHomAudit.ReviewedStatements.item_3_2_1, `PlanarHomAudit.ReviewedSolutions.item_3_2_1),
    ("3.2", `PlanarHomAudit.ReviewedStatements.item_3_2_2, `PlanarHomAudit.ReviewedSolutions.item_3_2_2),
    ("3.2", `PlanarHomAudit.ReviewedStatements.item_3_2_3, `PlanarHomAudit.ReviewedSolutions.item_3_2_3),
    ("3.3", `PlanarHomAudit.ReviewedStatements.item_3_3_1, `PlanarHomAudit.ReviewedSolutions.item_3_3_1),
    ("3.3", `PlanarHomAudit.ReviewedStatements.item_3_3_2, `PlanarHomAudit.ReviewedSolutions.item_3_3_2),
    ("3.5", `PlanarHomAudit.ReviewedStatements.item_3_5_1, `PlanarHomAudit.ReviewedSolutions.item_3_5_1),
    ("3.5", `PlanarHomAudit.ReviewedStatements.item_3_5_2, `PlanarHomAudit.ReviewedSolutions.item_3_5_2),
    ("3.5", `PlanarHomAudit.ReviewedStatements.item_3_5_3, `PlanarHomAudit.ReviewedSolutions.item_3_5_3),
    ("3.6", `PlanarHomAudit.ReviewedStatements.item_3_6_1, `PlanarHomAudit.ReviewedSolutions.item_3_6_1),
    ("3.6", `PlanarHomAudit.ReviewedStatements.item_3_6_2, `PlanarHomAudit.ReviewedSolutions.item_3_6_2),
    ("3.7", `PlanarHomAudit.ReviewedStatements.item_3_7_1, `PlanarHomAudit.ReviewedSolutions.item_3_7_1),
    ("3.7", `PlanarHomAudit.ReviewedStatements.item_3_7_2, `PlanarHomAudit.ReviewedSolutions.item_3_7_2),
    ("3.7", `PlanarHomAudit.ReviewedStatements.item_3_7_3, `PlanarHomAudit.ReviewedSolutions.item_3_7_3),
    ("3.7", `PlanarHomAudit.ReviewedStatements.item_3_7_4, `PlanarHomAudit.ReviewedSolutions.item_3_7_4),
    ("3.8", `PlanarHomAudit.ReviewedStatements.item_3_8_1, `PlanarHomAudit.ReviewedSolutions.item_3_8_1),
    ("3.8", `PlanarHomAudit.ReviewedStatements.item_3_8_2, `PlanarHomAudit.ReviewedSolutions.item_3_8_2),
    ("3.8", `PlanarHomAudit.ReviewedStatements.item_3_8_3, `PlanarHomAudit.ReviewedSolutions.item_3_8_3),
    ("3.8", `PlanarHomAudit.ReviewedStatements.item_3_8_4, `PlanarHomAudit.ReviewedSolutions.item_3_8_4),
    ("3.9", `PlanarHomAudit.ReviewedStatements.item_3_9_1, `PlanarHomAudit.ReviewedSolutions.item_3_9_1),
    ("3.10", `PlanarHomAudit.ReviewedStatements.item_3_10_1, `PlanarHomAudit.ReviewedSolutions.item_3_10_1),
    ("3.10", `PlanarHomAudit.ReviewedStatements.item_3_10_2, `PlanarHomAudit.ReviewedSolutions.item_3_10_2),
    ("3.10", `PlanarHomAudit.ReviewedStatements.item_3_10_3, `PlanarHomAudit.ReviewedSolutions.item_3_10_3),
    ("3.10", `PlanarHomAudit.ReviewedStatements.item_3_10_4, `PlanarHomAudit.ReviewedSolutions.item_3_10_4),
    ("3.11", `PlanarHomAudit.ReviewedStatements.item_3_11_1, `PlanarHomAudit.ReviewedSolutions.item_3_11_1),
    ("3.11", `PlanarHomAudit.ReviewedStatements.item_3_11_2, `PlanarHomAudit.ReviewedSolutions.item_3_11_2),
    ("4.1", `PlanarHomAudit.ReviewedStatements.item_4_1_1, `PlanarHomAudit.ReviewedSolutions.item_4_1_1),
    ("4.2", `PlanarHomAudit.ReviewedStatements.item_4_2_1, `PlanarHomAudit.ReviewedSolutions.item_4_2_1),
    ("4.2", `PlanarHomAudit.ReviewedStatements.item_4_2_2, `PlanarHomAudit.ReviewedSolutions.item_4_2_2),
    ("4.3", `PlanarHomAudit.ReviewedStatements.item_4_3_1, `PlanarHomAudit.ReviewedSolutions.item_4_3_1),
    ("4.4", `PlanarHomAudit.ReviewedStatements.item_4_4_1, `PlanarHomAudit.ReviewedSolutions.item_4_4_1),
    ("4.5", `PlanarHomAudit.ReviewedStatements.item_4_5_1, `PlanarHomAudit.ReviewedSolutions.item_4_5_1),
    ("4.6", `PlanarHomAudit.ReviewedStatements.item_4_6_1, `PlanarHomAudit.ReviewedSolutions.item_4_6_1),
    ("4.7", `PlanarHomAudit.ReviewedStatements.item_4_7_1, `PlanarHomAudit.ReviewedSolutions.item_4_7_1),
    ("4.8", `PlanarHomAudit.ReviewedStatements.item_4_8_1, `PlanarHomAudit.ReviewedSolutions.item_4_8_1),
    ("5.1", `PlanarHomAudit.ReviewedStatements.item_5_1_1, `PlanarHomAudit.ReviewedSolutions.item_5_1_1),
    ("6.1", `PlanarHomAudit.ReviewedStatements.item_6_1_1, `PlanarHomAudit.ReviewedSolutions.item_6_1_1),
    ("6.2", `PlanarHomAudit.ReviewedStatements.item_6_2_1, `PlanarHomAudit.ReviewedSolutions.item_6_2_1),
    ("7.1", `PlanarHomAudit.ReviewedStatements.item_7_1_1, `PlanarHomAudit.ReviewedSolutions.item_7_1_1),
    ("7.1", `PlanarHomAudit.ReviewedStatements.item_7_1_2, `PlanarHomAudit.ReviewedSolutions.item_7_1_2),
    ("8.1", `PlanarHomAudit.ReviewedStatements.item_8_1_1, `PlanarHomAudit.ReviewedSolutions.item_8_1_1),
    ("8.2", `PlanarHomAudit.ReviewedStatements.item_8_2_1, `PlanarHomAudit.ReviewedSolutions.item_8_2_1),
    ("8.3", `PlanarHomAudit.ReviewedStatements.item_8_3_1, `PlanarHomAudit.ReviewedSolutions.item_8_3_1),
    ("9.1", `PlanarHomAudit.ReviewedStatements.item_9_1_1, `PlanarHomAudit.ReviewedSolutions.item_9_1_1),
    ("9.2", `PlanarHomAudit.ReviewedStatements.item_9_2_1, `PlanarHomAudit.ReviewedSolutions.item_9_2_1),
    ("9.3", `PlanarHomAudit.ReviewedStatements.item_9_3_1, `PlanarHomAudit.ReviewedSolutions.item_9_3_1),
    ("11.1", `PlanarHomAudit.ReviewedStatements.item_11_1_1, `PlanarHomAudit.ReviewedSolutions.item_11_1_1),
    ("11.1", `PlanarHomAudit.ReviewedStatements.item_11_1_2, `PlanarHomAudit.ReviewedSolutions.item_11_1_2),
    ("11.1", `PlanarHomAudit.ReviewedStatements.item_11_1_3, `PlanarHomAudit.ReviewedSolutions.item_11_1_3),
    ("11.2", `PlanarHomAudit.ReviewedStatements.item_11_2_1, `PlanarHomAudit.ReviewedSolutions.item_11_2_1),
    ("11.2", `PlanarHomAudit.ReviewedStatements.item_11_2_2, `PlanarHomAudit.ReviewedSolutions.item_11_2_2),
    ("12.1", `PlanarHomAudit.ReviewedStatements.item_12_1_1, `PlanarHomAudit.ReviewedSolutions.item_12_1_1),
    ("12.2", `PlanarHomAudit.ReviewedStatements.item_12_2_1, `PlanarHomAudit.ReviewedSolutions.item_12_2_1),
    ("12.2", `PlanarHomAudit.ReviewedStatements.item_12_2_2, `PlanarHomAudit.ReviewedSolutions.item_12_2_2),
    ("12.2", `PlanarHomAudit.ReviewedStatements.item_12_2_3, `PlanarHomAudit.ReviewedSolutions.item_12_2_3),
    ("12.2", `PlanarHomAudit.ReviewedStatements.item_12_2_4, `PlanarHomAudit.ReviewedSolutions.item_12_2_4),
    ("12.2", `PlanarHomAudit.ReviewedStatements.item_12_2_5, `PlanarHomAudit.ReviewedSolutions.item_12_2_5),
    ("12.4", `PlanarHomAudit.ReviewedStatements.item_12_4_1, `PlanarHomAudit.ReviewedSolutions.item_12_4_1),
    ("12.4", `PlanarHomAudit.ReviewedStatements.item_12_4_2, `PlanarHomAudit.ReviewedSolutions.item_12_4_2),
    ("12.5", `PlanarHomAudit.ReviewedStatements.item_12_5_1, `PlanarHomAudit.ReviewedSolutions.item_12_5_1),
    ("12.6", `PlanarHomAudit.ReviewedStatements.item_12_6_1, `PlanarHomAudit.ReviewedSolutions.item_12_6_1),
    ("12.6", `PlanarHomAudit.ReviewedStatements.item_12_6_2, `PlanarHomAudit.ReviewedSolutions.item_12_6_2),
    ("12.7", `PlanarHomAudit.ReviewedStatements.item_12_7_1, `PlanarHomAudit.ReviewedSolutions.item_12_7_1),
    ("12.8", `PlanarHomAudit.ReviewedStatements.item_12_8_1, `PlanarHomAudit.ReviewedSolutions.item_12_8_1),
    ("12.8", `PlanarHomAudit.ReviewedStatements.item_12_8_2, `PlanarHomAudit.ReviewedSolutions.item_12_8_2),
    ("A.1", `PlanarHomAudit.ReviewedStatements.item_A_1_1, `PlanarHomAudit.ReviewedSolutions.item_A_1_1),
    ("A.2", `PlanarHomAudit.ReviewedStatements.item_A_2_1, `PlanarHomAudit.ReviewedSolutions.item_A_2_1),
    ("A.2", `PlanarHomAudit.ReviewedStatements.item_A_2_2, `PlanarHomAudit.ReviewedSolutions.item_A_2_2),
    ("A.2", `PlanarHomAudit.ReviewedStatements.item_A_2_3, `PlanarHomAudit.ReviewedSolutions.item_A_2_3),
    ("A.3", `PlanarHomAudit.ReviewedStatements.item_A_3_1, `PlanarHomAudit.ReviewedSolutions.item_A_3_1),
    ("A.4", `PlanarHomAudit.ReviewedStatements.item_A_4_1, `PlanarHomAudit.ReviewedSolutions.item_A_4_1),
    ("A.4", `PlanarHomAudit.ReviewedStatements.item_A_4_2, `PlanarHomAudit.ReviewedSolutions.item_A_4_2),
    ("A.4", `PlanarHomAudit.ReviewedStatements.item_A_4_3, `PlanarHomAudit.ReviewedSolutions.item_A_4_3),
    ("A.5", `PlanarHomAudit.ReviewedStatements.item_A_5_1, `PlanarHomAudit.ReviewedSolutions.item_A_5_1),
    ("A.5", `PlanarHomAudit.ReviewedStatements.item_A_5_2, `PlanarHomAudit.ReviewedSolutions.item_A_5_2),
    ("A.6", `PlanarHomAudit.ReviewedStatements.item_A_6_1, `PlanarHomAudit.ReviewedSolutions.item_A_6_1),
    ("A.7", `PlanarHomAudit.ReviewedStatements.item_A_7_1, `PlanarHomAudit.ReviewedSolutions.item_A_7_1),
    ("A.7", `PlanarHomAudit.ReviewedStatements.item_A_7_2, `PlanarHomAudit.ReviewedSolutions.item_A_7_2),
    ("A.7", `PlanarHomAudit.ReviewedStatements.item_A_7_3, `PlanarHomAudit.ReviewedSolutions.item_A_7_3),
    ("A.8", `PlanarHomAudit.ReviewedStatements.item_A_8_1, `PlanarHomAudit.ReviewedSolutions.item_A_8_1),
    ("A.8", `PlanarHomAudit.ReviewedStatements.item_A_8_2, `PlanarHomAudit.ReviewedSolutions.item_A_8_2),
    ("A.9", `PlanarHomAudit.ReviewedStatements.item_A_9_1, `PlanarHomAudit.ReviewedSolutions.item_A_9_1),
    ("A.9", `PlanarHomAudit.ReviewedStatements.item_A_9_2, `PlanarHomAudit.ReviewedSolutions.item_A_9_2),
    ("A.10", `PlanarHomAudit.ReviewedStatements.item_A_10_1, `PlanarHomAudit.ReviewedSolutions.item_A_10_1),
    ("A.11", `PlanarHomAudit.ReviewedStatements.item_A_11_1, `PlanarHomAudit.ReviewedSolutions.item_A_11_1),
    ("A.12", `PlanarHomAudit.ReviewedStatements.item_A_12_1, `PlanarHomAudit.ReviewedSolutions.item_A_12_1),
    ("A.13", `PlanarHomAudit.ReviewedStatements.item_A_13_1, `PlanarHomAudit.ReviewedSolutions.item_A_13_1),
    ("A.14", `PlanarHomAudit.ReviewedStatements.item_A_14_1, `PlanarHomAudit.ReviewedSolutions.item_A_14_1)]
  for (item, statement, solution) in targets do
    let some (.defnInfo spec) := env.find? statement
      | throwError m!"Missing fixed statement: {statement}"
    let some proof := env.find? solution
      | throwError m!"Missing solution: {solution}"
    unless spec.levelParams.length == proof.levelParams.length do
      throwError m!"Universe parameter mismatch for {solution}"
    let expected := spec.value.instantiateLevelParams spec.levelParams
      (proof.levelParams.map mkLevelParam)
    let equal ← liftTermElabM <| Meta.isDefEq expected proof.type
    unless equal do
      throwError m!"Reviewed statement mismatch: {solution} against {statement}"
    let (_, dependencies) := ((Lean.CollectAxioms.collect solution).run env).run {}
    for ax in dependencies.axioms do
      unless allowed.contains ax do
        throwError m!"Unexpected axiom {ax} in {solution}"
    let extra := Expr.forallE `extra (mkConst `True) expected BinderInfo.default
    let acceptsExtra ← liftTermElabM <| Meta.isDefEq extra proof.type
    if acceptsExtra then
      throwError m!"Extra premise accepted for {solution}"
    logInfo m!"REVIEWED_CONTRACT_PASS {item} {solution} == {statement}"
    logInfo m!"REVIEWED_EXTRA_PREMISE_REJECTED {solution}"
    logInfo m!"REVIEWED_CONTRACT_AXIOMS {solution}: {dependencies.axioms}"
