import PlanarHom
import Lean.Util.CollectAxioms

/-! Reproducible declaration/signature/axiom inventory for the 58 paper items.
Presence and allowed axioms alone do not establish correspondence with prose;
the item-by-item semantic review is in docs/PAPER_AUDIT.md. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let targets : Array (String × Array Name) := #[
    ("1.1", #[`PlanarHom.MainDichotomyScope.theorem11]),
    ("1.3", #[`PlanarHom.MainDichotomyScope.theorem13]),
    ("2.2", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.proposition22_i, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.proposition22_potts]),
    ("2.3", #[`PlanarHom.FixedRealSmallState.theorem23]),
    ("2.4", #[`PlanarHom.FixedRealSmallState.theorem24, `PlanarHom.FixedRealSmallState.theorem24_positive]),
    ("2.5", #[`PlanarHom.GadgetDiagonalSeparation.proposition25]),
    ("2.6", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.proposition26]),
    ("3.1", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma31_binary, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma31_unary, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma31_domain_binary, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma31_domain_unary]),
    ("3.2", #[`PlanarHom.Corollary32.support_chains, `PlanarHom.Corollary32.mixed_equivalence, `PlanarHom.Corollary32.joint_extremal_transforms]),
    ("3.3", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma33_range, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma33_rationalPower]),
    ("3.5", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma35_root, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma35_component, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma35_inFP]),
    ("3.6", #[`PlanarHom.tensorPower_linearIndependent, `PlanarHom.hadamard_weighted_gram_posDef]),
    ("3.7", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma37_inverseDiagonal, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma37_removeWeights, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma37_rational, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma37_finiteRationalPowers]),
    ("3.8", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary38_identity, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary38, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary38_zeroOne, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary38_zeroOne_hardnessLift]),
    ("3.9", #[`PlanarHom.lemma_3_9]),
    ("3.10", #[`PlanarHom.EffectiveProductTransfer.lemma310_polynomial_parameter, `PlanarHom.EffectiveProductTransfer.lemma310_spectral_parameter, `PlanarHom.EffectiveProductTransfer.lemma310_polynomial_domain_parameter, `PlanarHom.EffectiveProductTransfer.lemma310_spectral_domain_parameter]),
    ("3.11", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma311_source, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma311]),
    ("4.1", #[`PlanarHom.ClosedMatrixFamily.lemma41]),
    ("4.2", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma42_uniform, `PlanarHom.ClosedMatrixFamily.lemma42_structural]),
    ("4.3", #[`PlanarHom.ClosedMatrixFamily.lemma43]),
    ("4.4", #[`PlanarHom.ClosedMatrixFamily.lemma44]),
    ("4.5", #[`PlanarHom.KernelContinuation.posDef_distanceKernel]),
    ("4.6", #[`PlanarHom.CartesianGeometry.cartesian_product_characterization]),
    ("4.7", #[`PlanarHom.ClosedMatrixFamily.lemma47]),
    ("4.8", #[`PlanarHom.ClosedMatrixFamily.proposition48_fixed_maximum]),
    ("5.1", #[`PlanarHom.BooleanTensorDichotomy.theorem5_1_literal]),
    ("6.1", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem61]),
    ("6.2", #[`PlanarHom.ClosedMatrixFamily.corollary62]),
    ("7.1", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem71_weighted, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem71_unweighted]),
    ("8.1", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.theorem81]),
    ("8.2", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma82]),
    ("8.3", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma83]),
    ("9.1", #[`PlanarHom.RectangularUnweightedSourceForms.theorem91]),
    ("9.2", #[`PlanarHom.RectangularCoreSourceRigidity.proposition92]),
    ("9.3", #[`PlanarHom.PrescribedTensorWeight.lemma93]),
    ("11.1", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma111_a, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma111_b, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.lemma111_c]),
    ("11.2", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary112, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.empty_surviving_evaluate]),
    ("12.1", #[`PlanarHom.TargetGraphDichotomy.corollary121]),
    ("12.2", #[`PlanarHom.DomainDoublingClassification.corollary122_bipartite, `PlanarHom.DomainDoublingClassification.corollary122_prescribed, `PlanarHom.DomainDoublingClassification.corollary122_rectangular, `PlanarHom.DomainDoublingClassification.corollary122_bipartite_unweighted, `PlanarHom.DomainDoublingClassification.corollary122_prescribed_unweighted]),
    ("12.4", #[`PlanarHom.CenteredLogStructural.lemma124_structure_and_rank, `PlanarHom.CenteredLogStructural.tensor_form_inFP]),
    ("12.5", #[`PlanarHom.FixedRealClock.corollary125]),
    ("12.6", #[`PlanarHom.FixedRealCoupledIsing.corollary126_set, `PlanarHom.FixedRealCoupledIsing.empty_labels_inFP]),
    ("12.7", #[`PlanarHom.FixedRealBlumeCapel.corollary127]),
    ("12.8", #[`PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary128_unweighted, `PlanarHom.AlgebraicProductInterpolation.RealLanguage.corollary128_weighted]),
    ("A.1", #[`PlanarHom.FixedRealLemmaA1.lemmaA1]),
    ("A.2", #[`PlanarHom.FixedRealMixedRootRestriction.corollaryA2_mixed_root_prescribed, `PlanarHom.FixedRealMixedRootRestriction.corollaryA2_mixed_submatrix_prescribed, `PlanarHom.FixedRealMixedOrientation.corollaryA2_mixed_orientation_prescribed]),
    ("A.3", #[`PlanarHom.FixedRealMixedInterpolation.theoremA3_prescribed_joint]),
    ("A.4", #[`PlanarHom.RelationApproximation.relation_preserving_approximation, `PlanarHom.FixedRealApproximation.theoremA4_joint, `PlanarHom.FixedRealApproximation.theoremA4_prescribed_rational]),
    ("A.5", #[`PlanarHom.FixedChartClosedness.isClosed_nonnegativeClass_support, `PlanarHom.FixedChartClosedness.nonnegativeClass_of_tendsto_fixedSupport]),
    ("A.6", #[`PlanarHom.FixedRealApproximation.theoremA6]),
    ("A.7", #[`PlanarHom.FixedRealSignedTransforms.theoremA7_all_five, `PlanarHom.FixedRealSignedTransforms.theoremA7_chain, `PlanarHom.FixedRealSignedTransforms.theoremA7_mixed_equivalence]),
    ("A.8", #[`PlanarHom.FixedRealWeightRemoval.theoremA8, `PlanarHom.FixedRealWeightRemoval.constructedPowers_joint]),
    ("A.9", #[`PlanarHom.FixedRealSupportHardness.theoremA9_zeroOne, `PlanarHom.FixedRealSupportHardness.theoremA9_hard]),
    ("A.10", #[`PlanarHom.FixedRealLemmaA10.lemmaA10]),
    ("A.11", #[`PlanarHom.FixedRealLemmaA11.lemmaA11]),
    ("A.12", #[`PlanarHom.FixedRealWeightedClassification.theoremA12]),
    ("A.13", #[`PlanarHom.FixedRealSurvivingWeights.theoremA13]),
    ("A.14", #[`PlanarHom.FixedRealSignedConsequences.theoremA14])]
  for (item, names) in targets do
    for target in names do
      let some info := env.find? target | throwError m!"Missing paper target: {target}"
      let (_, dependencies) := ((Lean.CollectAxioms.collect target).run env).run {}
      for ax in dependencies.axioms do
        unless allowed.contains ax do
          throwError m!"Unexpected axiom {ax} in paper item {item}: {target}"
      logInfo m!"PAPER_TARGET {item} {target}"
      logInfo m!"PAPER_TYPE {target}: {info.type}"
      logInfo m!"PAPER_AXIOMS {target}: {dependencies.axioms}"
    logInfo m!"PAPER_ITEM_CHECKED {item}"
