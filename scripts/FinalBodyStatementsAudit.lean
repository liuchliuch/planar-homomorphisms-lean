import PlanarHom
import Lean.Util.CollectAxioms

#check @PlanarHom.TargetGraphDichotomy.corollary121
#check @PlanarHom.SurfacePlanarHardness.reduction
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary128_unweighted
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary128_weighted
#check @PlanarHom.SignedThreeState.theorem23_algebraic
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem2_4
#check @PlanarHom.ClockModel.corollary125_algebraic
#check @PlanarHom.CoupledIsing.corollary126_algebraic
#check @PlanarHom.BlumeCapel.corollary127_algebraic

#print axioms PlanarHom.TargetGraphDichotomy.corollary121
#print axioms PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary128_unweighted
#print axioms PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary128_weighted

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
  logInfo "FINAL_BODY_STATEMENTS_IMPORTED_DECLARATIONS_STANDARD_AXIOMS_PASS"
