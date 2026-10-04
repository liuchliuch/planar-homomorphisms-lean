/- NEW axiom audit for executable parity elimination. -/
import PlanarHom.PlanarityParityRegressions
import PlanarHom.PlanarityLRBlockRegressions
import PlanarHom.PlanarityLRRotationRegressions
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
  logInfo "RECONSTRUCTED_PLANARITY_LR_ROTATION_AXIOM_AUDIT_PASS: only propext, Classical.choice, Quot.sound"

#check PlanarHom.PlanarityParitySolver.computed_sound
#check PlanarHom.PlanarityParitySolver.computed_complete
#check PlanarHom.PlanarityParitySolver.fp_computed
#print axioms PlanarHom.PlanarityParitySolver.fp_computed
#print axioms PlanarHom.PlanarityParitySolver.computed_complete

#check PlanarHom.PlanarityLRConstraintBlocks.decideBlocks_sound
#check PlanarHom.PlanarityLRConstraintBlocks.decideBlocks_complete
#check PlanarHom.PlanarityLRConstraintBlocks.fp_decideBlocks
#print axioms PlanarHom.PlanarityLRConstraintBlocks.fp_decideBlocks

#check PlanarHom.PlanarityLRRawConstraints.solveLR_sound
#check PlanarHom.PlanarityLRRawConstraints.solveLR_complete
#print axioms PlanarHom.PlanarityLRRawConstraints.solveLR_complete

#check PlanarHom.PlanarityLRRawConstraints.tree_source_parent
#check PlanarHom.PlanarityLRRawConstraints.back_target_ancestor
#check PlanarHom.PlanarityLRRawConstraints.lowpoint_back
#check PlanarHom.PlanarityLRConstraintBlocks.exists_aligned_iff
#check PlanarHom.PlanarityLRConstraintBlocks.fp_decideAlignedBlocks

#check PlanarHom.PlanarityLRRawConstraints.alignmentPairs_safe
#check PlanarHom.PlanarityLRRawConstraints.solveAlignedLR_complete
#check PlanarHom.PlanarityLRConstraints.decideAligned_sound
#check PlanarHom.PlanarityLRConstraints.decideAligned_complete
#print axioms PlanarHom.PlanarityLRRawConstraints.alignmentPairs_safe

#check PlanarHom.PlanarityLRDirect.directRow_nodup
#check PlanarHom.PlanarityLRDirect.mem_directRow
#check PlanarHom.PlanarityLRDirect.directRow_perm_incident
#check PlanarHom.PlanarityLRDirect.treeInsertion_source_available
#check PlanarHom.PlanarityLRDirect.treeInsertion_target_fresh
#check PlanarHom.PlanarityLRRealization.directRotationRows
#check PlanarHom.PlanarityLRRealization.directRotationRows_erase
#print axioms PlanarHom.PlanarityLRRealization.directRotationRows_erase
#check PlanarHom.PlanarityLRDirect.fp_edgeSide
