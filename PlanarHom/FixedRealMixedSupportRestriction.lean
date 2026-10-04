import PlanarHom.MixedCommonSupportPropagation
import PlanarHom.RepresentedQueryReduction
import PlanarHom.RepresentedReductionComposition

/-! Whole-input common-support extraction for a retained finite mixed language.
Every binary label must preserve the selected set; no arbitrary root-set pinning
is promoted to an induced-submatrix reduction. Unaries remain unrestricted. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealMixedRootRestriction
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit MixedRootedRestriction
variable {n e b u:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def connectedSubmatrixToRoot (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (X:Set C) (hX:CommonClosed M X) :
    Reduction (FixedRealComponents.connectedProblem basis (fun l (i j:X)=>M l i.val j.val)
      (fun l (i:X)=>U l i.val) (fun i:X=>w i.val)) (rootProblem basis M U w X) := by
  apply queryReduction (presentation basis) MixedCode.encoding RootedCodeMachines.inputEncoding MixedCode.normalizer
    (FixedRealComponents.connectedValid (b:=b) (u:=u)) (inputValid (b:=b) (u:=u))
    (totalEvaluation (fun l (i j:X)=>M l i.val j.val) (fun l (i:X)=>U l i.val) (fun i:X=>w i.val))
    (rootValue M U w X) (fun g=>(0,g)) ((fp_const _ _ 0).pair (fp_id _))
  · intro g hg
    exact ⟨hg.1,hg.2.2⟩
  · intro g hg
    rw [rootValue,dif_pos hg.1.1,dif_pos hg.2.2,
      MixedRootedRestriction.rootRestricted_eq_submatrix g hg.1.1 hg.2.1 ⟨0,hg.2.2⟩ M hs U w X hX,
      totalEvaluation_valid _ _ _ _ hg.1.1]

variable [LinearOrder K] [IsStrictOrderedRing K]

def submatrixReduction (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (hw:∀i,0 < w i) (X:Set C) (hX:CommonClosed M X) :
    Reduction (FixedRealComponents.problem basis (fun l (i j:X)=>M l i.val j.val)
      (fun l (i:X)=>U l i.val) (fun i:X=>w i.val)) (FixedRealComponents.problem basis M U w) :=
  ((FixedRealComponents.componentReduction basis (fun l (i j:X)=>M l i.val j.val)
    (fun l (i:X)=>U l i.val) (fun i:X=>w i.val)).trans
    (connectedSubmatrixToRoot basis M hs U w X hX)).trans (corollaryA2_mixed_root basis M U w hw X)

/-- The common support component is taken in the union of supports of every
retained matrix, exactly the propagation required by the mixed-language scope. -/
def corollaryA2_mixed_component (M:Fin b→Matrix C C K) (hs:∀l i j,M l i j=M l j i)
    (U:Fin u→C→K) (w:C→K) (hw:∀i,0 < w i) (c:(commonSupport M hs).ConnectedComponent) :
    Reduction (FixedRealComponents.problem basis (fun l (i j:c.supp)=>M l i.val j.val)
      (fun l (i:c.supp)=>U l i.val) (fun i:c.supp=>w i.val)) (FixedRealComponents.problem basis M U w) :=
  submatrixReduction basis M hs U w hw c.supp (component_commonClosed M hs c)

end PlanarHom.FixedRealMixedRootRestriction
