import PlanarHom.FixedRealMixedOrientationReduction
import PlanarHom.FixedRealMixedRootPrescribedFields

/-! Prescribed-presentation full mixed bipartite orientation. Intrinsic side
indicators map to the same zero/one indicators in the common working field;
ordinary retained labels/weights agree under the explicit embeddings. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealMixedOrientation
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open PrescribedDomains FixedRealRootRestrictions MixedOrientation
variable {d e c f s z b u:ℕ} {K F S C:Type} [Field K] [Field F] [Field S] [Fintype C]
variable [Algebra (RationalFunction d) K] [Algebra (RationalFunction c) F] [Algebra (RationalFunction s) S]
variable [LinearOrder K] [IsStrictOrderedRing K]

def corollaryA2_mixed_orientation_prescribed
    (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (targetBasis:Module.Basis (Fin f) (RationalFunction c) F) (targetEmbed:F→+*K)
    (sourceBasis:Module.Basis (Fin z) (RationalFunction s) S) (sourceEmbed:S→+*K)
    (MS:Fin b→Matrix C C S) (US:Fin u→C→S) (wS:C→S)
    (MT:Fin b→Matrix C C F) (UT:Fin u→C→F) (wT:C→F)
    (hM:(fun l i j=>targetEmbed (MT l i j))=(fun l i j=>sourceEmbed (MS l i j)))
    (hU:(fun l i=>targetEmbed (UT l i))=(fun l i=>sourceEmbed (US l i)))
    (hw:(fun i=>targetEmbed (wT i))=(fun i=>sourceEmbed (wS i)))
    (hpos:∀i,0 < sourceEmbed (wS i))
    (hs:∀l i j,sourceEmbed (MS l i j)=sourceEmbed (MS l j i))
    (side:C→Bool) (hcross:∀l i j,sourceEmbed (MS l i j)≠0→side i≠side j) :
    Reduction (problem targetBasis MT UT wT side) (FixedRealComponents.problem sourceBasis MS US wS) := by
  apply FixedRealPresentationReductions.prescribedReduction ambient targetBasis targetEmbed sourceBasis sourceEmbed
    MixedCode.encoding MixedCode.encoding MixedCode.normalizer MixedCode.normalizer
    (EncodedGraph (sidePolicies b) (unaryPolicies u)) (PlanarValid b u)
    (totalEvaluation MT (extendedUnaries UT (Bipartite.domains side)) wT) (totalEvaluation MS US wS)
  have ht:=funext (FixedRealMixedPresentationTransport.map_totalEvaluation targetEmbed
    MT (extendedUnaries UT (Bipartite.domains side)) wT)
  rw [map_extendedUnaries] at ht
  rw [hM,hU,hw] at ht
  have hsource:=funext (FixedRealMixedPresentationTransport.map_totalEvaluation sourceEmbed MS US wS)
  rw [ht,hsource]
  exact corollaryA2_mixed_orientation ambient _ hs _ _ hpos side hcross

end PlanarHom.FixedRealMixedOrientation
