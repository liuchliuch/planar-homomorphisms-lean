import PlanarHom.FixedRealMixedSupportRestriction
import PlanarHom.FixedRealMixedPresentationTransport

/-! Prescribed-field A.2 root and common-support extraction. The source oracle
keeps its original presentation, and the requested answer is converted to the
target's specified field presentation by the actual two-sided wrapper. -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealMixedRootRestriction
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit MixedRootedRestriction
variable {d e c f s z b u:ℕ} {K F S C:Type} [Field K] [Field F] [Field S] [Fintype C]
variable [Algebra (RationalFunction d) K] [Algebra (RationalFunction c) F] [Algebra (RationalFunction s) S]

theorem map_rootValue {L R:Type} [Field L] [Field R] (φ:L→+*R)
    (M:Fin b→Matrix C C L) (U:Fin u→C→L) (w:C→L) (X:Set C) (p:ℕ×MixedCode) :
    φ (rootValue M U w X p)=rootValue (fun l i j=>φ (M l i j)) (fun l i=>φ (U l i)) (fun i=>φ (w i)) X p := by
  unfold rootValue
  split
  · split
    · simp only [MixedInstance.rootRestricted,map_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      split
      · simp only [MixedInstance.assignment,map_mul,map_prod]
      · exact map_zero φ
    · exact map_zero φ
  · exact map_zero φ

variable [LinearOrder K] [IsStrictOrderedRing K]

def corollaryA2_mixed_root_prescribed
    (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (targetBasis:Module.Basis (Fin f) (RationalFunction c) F) (targetEmbed:F→+*K)
    (sourceBasis:Module.Basis (Fin z) (RationalFunction s) S) (sourceEmbed:S→+*K)
    (MS:Fin b→Matrix C C S) (US:Fin u→C→S) (wS:C→S)
    (MT:Fin b→Matrix C C F) (UT:Fin u→C→F) (wT:C→F)
    (hM:(fun l i j=>targetEmbed (MT l i j))=(fun l i j=>sourceEmbed (MS l i j)))
    (hU:(fun l i=>targetEmbed (UT l i))=(fun l i=>sourceEmbed (US l i)))
    (hw:(fun i=>targetEmbed (wT i))=(fun i=>sourceEmbed (wS i)))
    (hpos:∀i,0 < sourceEmbed (wS i)) (X:Set C) :
    Reduction (rootProblem targetBasis MT UT wT X) (FixedRealComponents.problem sourceBasis MS US wS) := by
  apply FixedRealPresentationReductions.prescribedReduction ambient targetBasis targetEmbed sourceBasis sourceEmbed
    RootedCodeMachines.inputEncoding MixedCode.encoding
    (BitEncoding.prodNormalizer BitEncoding.natNormalizer MixedCode.normalizer) MixedCode.normalizer
    (inputValid (b:=b) (u:=u)) (PlanarValid b u) (rootValue MT UT wT X) (totalEvaluation MS US wS)
  have ht:(fun p=>targetEmbed (rootValue MT UT wT X p))=
      rootValue (fun l i j=>targetEmbed (MT l i j)) (fun l i=>targetEmbed (UT l i)) (fun i=>targetEmbed (wT i)) X:=
    funext (map_rootValue targetEmbed MT UT wT X)
  have hsource:(fun g=>sourceEmbed (totalEvaluation MS US wS g))=
      totalEvaluation (fun l i j=>sourceEmbed (MS l i j)) (fun l i=>sourceEmbed (US l i)) (fun i=>sourceEmbed (wS i)):=
    funext (FixedRealMixedPresentationTransport.map_totalEvaluation sourceEmbed MS US wS)
  rw [ht,hsource,hM,hU,hw]
  exact corollaryA2_mixed_root ambient _ _ _ hpos X

def corollaryA2_mixed_submatrix_prescribed
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
    (X:Set C) (hX:CommonClosed (fun l i j=>sourceEmbed (MS l i j)) X) :
    Reduction (FixedRealComponents.problem targetBasis (fun l (i j:X)=>MT l i.val j.val)
      (fun l (i:X)=>UT l i.val) (fun i:X=>wT i.val)) (FixedRealComponents.problem sourceBasis MS US wS) := by
  apply FixedRealPresentationReductions.prescribedReduction ambient targetBasis targetEmbed sourceBasis sourceEmbed
    MixedCode.encoding MixedCode.encoding MixedCode.normalizer MixedCode.normalizer (PlanarValid b u) (PlanarValid b u)
    (totalEvaluation (fun l (i j:X)=>MT l i.val j.val) (fun l (i:X)=>UT l i.val) (fun i:X=>wT i.val))
    (totalEvaluation MS US wS)
  have ht:=funext (FixedRealMixedPresentationTransport.map_totalEvaluation targetEmbed
    (fun l (i j:X)=>MT l i.val j.val) (fun l (i:X)=>UT l i.val) (fun i:X=>wT i.val))
  have hsource:=funext (FixedRealMixedPresentationTransport.map_totalEvaluation sourceEmbed MS US wS)
  rw [ht,hsource]
  have hMr:∀l i j,targetEmbed (MT l i j)=sourceEmbed (MS l i j):=fun l i j=>congrFun (congrFun (congrFun hM l) i) j
  have hUr:∀l i,targetEmbed (UT l i)=sourceEmbed (US l i):=fun l i=>congrFun (congrFun hU l) i
  have hwr:∀i,targetEmbed (wT i)=sourceEmbed (wS i):=congrFun hw
  simp only [hMr,hUr,hwr]
  exact submatrixReduction ambient (fun l i j=>sourceEmbed (MS l i j)) hs
    (fun l i=>sourceEmbed (US l i)) (fun i=>sourceEmbed (wS i)) hpos X hX

end PlanarHom.FixedRealMixedRootRestriction
