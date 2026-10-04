import PlanarHom.PlanarityLRRoutingAxiomAudit
import PlanarHom.PlanarityLRContourPermutation
import PlanarHom.PlanarityLRNoninterleavingIntervals
import PlanarHom.PlanarityLROutgoingOrder
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
  logInfo "RECONSTRUCTED_PLANARITY_LR_CONTOUR_AXIOM_AUDIT_PASS"
#check PlanarHom.PlanarityLRRealization.contourPermutation
#check PlanarHom.PlanarityLRRealization.contourPortWord_nodup
#check PlanarHom.PlanarityLRRealization.mem_contourPortWord_iff
#check PlanarHom.PlanarityLRRealization.noninterleaving_iff_not_alternating
#check PlanarHom.PlanarityLRDirect.orderedOutgoing_rank_lt_iff
#check PlanarHom.PlanarityLRDirect.same_side_return_separation
#check PlanarHom.PlanarityLRDirect.same_side_lower_return_bound
#check PlanarHom.PlanarityLRDirect.same_lowpoint_chordal_sides_ne
#print axioms PlanarHom.PlanarityLRDirect.same_side_lower_return_bound
