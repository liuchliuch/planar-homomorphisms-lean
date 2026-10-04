import PlanarHom.LRWordsRegressions
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
    if (`PlanarHom).isPrefixOf name || (`ReimplementedLRWords).isPrefixOf name ||
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
  logInfo "LR_WORD_PREFIX_FOUNDATIONS_AUDIT_PASS"
#print axioms PlanarHom.PlanarityLRDirect.rootPath_prefix_iff_desc
#print axioms PlanarHom.PlanarityLRDirect.treeWord_parent
#print axioms PlanarHom.PlanarityLRDirect.treeWord_injective
#print axioms PlanarHom.PlanarityLRDirect.treeWord_prefix_iff_desc
#print axioms PlanarHom.PlanarityLRDirect.backWord_prefix_free
#print axioms PlanarHom.PlanarityLRDirect.backWord_injective

#print axioms PlanarHom.PlanarityLRDirect.backWord_not_prefix_treeWord
#print axioms PlanarHom.PlanarityLRDirect.treeWord_prefix_backWord_iff_desc
