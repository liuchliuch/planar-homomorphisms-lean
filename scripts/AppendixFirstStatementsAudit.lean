import PlanarHom
import Lean.Util.CollectAxioms

#check @PlanarHom.FixedRealSmallState.theorem23
#check @PlanarHom.FixedRealSmallState.theorem24
#check @PlanarHom.FixedRealLemmaA1.lemmaA1
#check @PlanarHom.FixedRealApproximation.theoremA4_prescribed_rational
#check @PlanarHom.FixedRealMixedInterpolation.theoremA3_prescribed_joint
#check @PlanarHom.FixedRealApproximation.theoremA4
#check @PlanarHom.FixedRealApproximation.theoremA6
#check @PlanarHom.FixedRealSignedTransforms.theoremA7_all_five
#check @PlanarHom.FixedRealSignedTransforms.theoremA7_chain
#check @PlanarHom.FixedRealWeightRemoval.theoremA8
#check @PlanarHom.FixedRealSupportHardness.theoremA9_hard
#check @PlanarHom.FixedRealSupportHardness.theoremA9_zeroOne
#check @PlanarHom.FixedRealLemmaA10.lemmaA10
#check @PlanarHom.FixedRealLemmaA11.lemmaA11
#check @PlanarHom.FixedRealSignedConsequences.theoremA14

#print axioms PlanarHom.FixedRealSmallState.theorem23
#print axioms PlanarHom.FixedRealSmallState.theorem24
#print axioms PlanarHom.FixedRealLemmaA1.lemmaA1
#print axioms PlanarHom.FixedRealMixedInterpolation.theoremA3_prescribed_joint
#print axioms PlanarHom.FixedRealApproximation.theoremA4
#print axioms PlanarHom.FixedRealApproximation.theoremA6
#print axioms PlanarHom.FixedRealSignedTransforms.theoremA7_all_five
#print axioms PlanarHom.FixedRealSignedTransforms.theoremA7_chain
#print axioms PlanarHom.FixedRealWeightRemoval.theoremA8
#print axioms PlanarHom.FixedRealSupportHardness.theoremA9_hard
#print axioms PlanarHom.FixedRealSupportHardness.theoremA9_zeroOne
#print axioms PlanarHom.FixedRealLemmaA10.lemmaA10
#print axioms PlanarHom.FixedRealLemmaA11.lemmaA11
#print axioms PlanarHom.FixedRealSignedConsequences.theoremA14

#check @PlanarHom.FixedRealClock.corollary125
#print axioms PlanarHom.FixedRealClock.corollary125
#check @PlanarHom.FixedRealClock.corollary125_unit
#print axioms PlanarHom.FixedRealClock.corollary125_unit
#check @PlanarHom.FixedRealCoupledIsing.corollary126_set
#print axioms PlanarHom.FixedRealCoupledIsing.corollary126_set
#check @PlanarHom.FixedRealCoupledIsing.corollary126_set_unit
#print axioms PlanarHom.FixedRealCoupledIsing.corollary126_set_unit
#check @PlanarHom.FixedRealCoupledIsing.empty_labels_inFP
#print axioms PlanarHom.FixedRealCoupledIsing.empty_labels_inFP
#check @PlanarHom.FixedRealBlumeCapel.corollary127
#print axioms PlanarHom.FixedRealBlumeCapel.corollary127
#check @PlanarHom.FixedRealMixedRootRestriction.corollaryA2_mixed_root_prescribed
#print axioms PlanarHom.FixedRealMixedRootRestriction.corollaryA2_mixed_root_prescribed
#check @PlanarHom.FixedRealMixedRootRestriction.corollaryA2_mixed_submatrix_prescribed
#print axioms PlanarHom.FixedRealMixedRootRestriction.corollaryA2_mixed_submatrix_prescribed
#check @PlanarHom.FixedRealMixedOrientation.corollaryA2_mixed_orientation_prescribed
#print axioms PlanarHom.FixedRealMixedOrientation.corollaryA2_mixed_orientation_prescribed

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut n := 0
  let mut thms := 0
  let mut state : Lean.CollectAxioms.State := {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for m in env.header.moduleNames do
    if (`PlanarHom).isPrefixOf m then logInfo m!"AUDITED_MODULE {m}"
  for (name, _) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => (`PlanarHom).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if origin then
      let (_, s) := ((Lean.CollectAxioms.collect name).run env).run state
      state := s
      for ax in state.axioms do
        unless allowed.contains ax do
          throwError m!"Unexpected axiom {ax}, discovered at {name}"
      n := n+1
      if Lean.wasOriginallyTheorem env name then thms := thms+1
  logInfo m!"PROJECT_DECLARATION_COUNT={n}"
  logInfo m!"PROJECT_THEOREM_COUNT={thms}"
  logInfo m!"AXIOM_UNION={state.axioms}"
  logInfo "APPENDIX_FIRST_STATEMENTS_IMPORTED_DECLARATIONS_STANDARD_AXIOMS_PASS"
