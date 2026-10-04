import PlanarHom.LRIntervalsRegressions
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut ds := 0
  let mut ts := 0
  let mut state : Lean.CollectAxioms.State := {}
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for (name,_) in env.constants.toList do
    if (`PlanarHom).isPrefixOf name || (`ReimplementedLRIntervals).isPrefixOf name ||
        name.toString.startsWith "_private.PlanarHom." ||
        name.toString.startsWith "_private.Regressions." then
      let (_,s) := ((Lean.CollectAxioms.collect name).run env).run state
      state := s
      for ax in state.axioms do
        unless allowed.contains ax do throwError m!"Unexpected axiom {ax} at {name}"
      ds := ds+1
      if Lean.wasOriginallyTheorem env name then ts := ts+1
  logInfo m!"AXIOM_UNION={state.axioms}"
  logInfo m!"DECLARATIONS={ds}; THEOREMS={ts}"
  logInfo "LR_SUBTREE_INTERVAL_ORDER_AUDIT_PASS"
#print axioms PlanarHom.NatWordPrefix.convex
#print axioms PlanarHom.PlanarityLRDirect.subtree_event_interval
#print axioms PlanarHom.PlanarityLRDirect.treeBranch_event_rank_lt_iff
#print axioms PlanarHom.PlanarityLRDirect.treeReturn_event_rank_lt_iff
