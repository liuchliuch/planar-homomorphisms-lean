import PlanarHom
import Lean.Util.CollectAxioms

#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.proposition22_i
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.proposition22_potts
#check @PlanarHom.GadgetDiagonalSeparation.proposition25
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.proposition26
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma311_source
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma311
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem61
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.positiveDefiniteForm_iff_displayed
#check @PlanarHom.ClosedMatrixFamily.corollary62
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem71_weighted
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem71_unweighted
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem81
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma82
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma83
#check @PlanarHom.RectangularUnweightedSourceForms.theorem91
#check @PlanarHom.RectangularCoreSourceRigidity.proposition92
#check @PlanarHom.PrescribedTensorWeight.lemma93
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma111_a
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma111_b
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma111_c
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary112
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.empty_surviving_evaluate
#check @PlanarHom.DomainDoublingClassification.corollary122_bipartite
#check @PlanarHom.DomainDoublingClassification.corollary122_prescribed
#check @PlanarHom.DomainDoublingClassification.corollary122_rectangular
#check @PlanarHom.DomainDoublingClassification.corollary122_bipartite_unweighted
#check @PlanarHom.DomainDoublingClassification.corollary122_prescribed_unweighted
#check @PlanarHom.DomainDoublingClassification.equation121
#check @PlanarHom.CenteredLogStructural.lemma124_structure_and_rank
#check @PlanarHom.CenteredLogStructural.tensor_form_inFP
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem2_4
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem2_4_positive
#check @PlanarHom.AlgebraicProductInterpolation.RealLanguage.directSum_block_algorithms

#print axioms PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary112
#print axioms PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem71_unweighted
#print axioms PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem2_4

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
  logInfo "BODY_STATEMENTS_IMPORTED_DECLARATIONS_STANDARD_AXIOMS_PASS"
