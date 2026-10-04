import PlanarHom.DirectRotationRegressions
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
    if (`PlanarHom).isPrefixOf name || (`ReimplementedDirectRuntime).isPrefixOf name ||
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
  logInfo "DIRECT_ROTATION_RUNTIME_AUDIT_PASS"
#print axioms PlanarHom.NatWordComparisonMachines.fp_lex
#print axioms PlanarHom.DynamicListIndexMachines.fp_index
#print axioms PlanarHom.PlanarityLRDirect.fp_directRow
#print axioms PlanarHom.PlanarityLRDirect.fp_directRotation
#print axioms PlanarHom.PlanarityLRDirect.fp_faceStep
#print axioms PlanarHom.PlanarityLRDirect.eventLE_trans

#print axioms PlanarHom.PlanarityLRDirect.fp_decidedRows
#print axioms PlanarHom.PlanarityLRDirect.fp_decidedFaceStep
