import PlanarHom.FixedRealPresentationReductions
import PlanarHom.FixedRealMixedInterpolation
import PlanarHom.MixedEvaluationFieldMap

/-! Prescribed source/target field transport for actual mixed graph evaluations.
The equalities used by the generic answer converter are proved on every raw
code, including malformed codes, not supplied as an oracle-reencoding premise. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealMixedPresentationTransport
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
variable {d e c f s r q b₁ u₁ b₂ u₂:ℕ} {K F S:Type} [Field K] [Field F] [Field S]
variable [Algebra (RationalFunction d) K] [Algebra (RationalFunction c) F] [Algebra (RationalFunction s) S]

theorem map_totalEvaluation {A B C:Type} [Field A] [Field B] [Fintype C] {b u:ℕ}
    (φ:A→+*B) (M:Fin b→Matrix C C A) (U:Fin u→C→A) (w:C→A) (g:MixedCode) :
    φ (totalEvaluation M U w g)=totalEvaluation (fun l i j=>φ (M l i j)) (fun l i=>φ (U l i)) (fun i=>φ (w i)) g := by
  by_cases hg:g.Valid b u
  · rw [totalEvaluation_valid _ _ _ g hg,totalEvaluation_valid _ _ _ g hg]
    exact map_evaluate φ g hg M U w
  · simp [totalEvaluation,hg]

def reduction (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (targetBasis:Module.Basis (Fin f) (RationalFunction c) F) (targetEmbed:F→+*K)
    (sourceBasis:Module.Basis (Fin r) (RationalFunction s) S) (sourceEmbed:S→+*K)
    (MT:Fin b₁→Matrix (Fin q) (Fin q) F) (UT:Fin u₁→Fin q→F) (wT:Fin q→F)
    (MS:Fin b₂→Matrix (Fin q) (Fin q) S) (US:Fin u₂→Fin q→S) (wS:Fin q→S)
    (common:Reduction
      (FixedRealMixedInterpolation.problem ambient (fun l i j=>targetEmbed (MT l i j))
        (fun l i=>targetEmbed (UT l i)) (fun i=>targetEmbed (wT i)))
      (FixedRealMixedInterpolation.problem ambient (fun l i j=>sourceEmbed (MS l i j))
        (fun l i=>sourceEmbed (US l i)) (fun i=>sourceEmbed (wS i)))) :
    Reduction (FixedRealMixedInterpolation.problem targetBasis MT UT wT)
      (FixedRealMixedInterpolation.problem sourceBasis MS US wS) := by
  apply FixedRealPresentationReductions.prescribedReduction ambient targetBasis targetEmbed sourceBasis sourceEmbed
    MixedCode.encoding MixedCode.encoding MixedCode.normalizer MixedCode.normalizer
    (PlanarValid b₁ u₁) (PlanarValid b₂ u₂) (totalEvaluation MT UT wT) (totalEvaluation MS US wS)
  have ht:(fun g=>targetEmbed (totalEvaluation MT UT wT g))=
      totalEvaluation (fun l i j=>targetEmbed (MT l i j)) (fun l i=>targetEmbed (UT l i)) (fun i=>targetEmbed (wT i)):=
    funext (map_totalEvaluation targetEmbed MT UT wT)
  have hs:(fun g=>sourceEmbed (totalEvaluation MS US wS g))=
      totalEvaluation (fun l i j=>sourceEmbed (MS l i j)) (fun l i=>sourceEmbed (US l i)) (fun i=>sourceEmbed (wS i)):=
    funext (map_totalEvaluation sourceEmbed MS US wS)
  rw [ht,hs]
  exact common

end PlanarHom.FixedRealMixedPresentationTransport
