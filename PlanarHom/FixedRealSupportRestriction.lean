import PlanarHom.FixedRealComponentReduction
import PlanarHom.FixedRealRootRestriction
import PlanarHom.RepresentedQueryReduction
import PlanarHom.RepresentedReductionComposition
import PlanarHom.RootedColorRestriction

/-! Ordinary-input support-component extraction in the represented fixed-real
model. Actual connected-component queries and one root restriction per queried
component preserve empty inputs and isolated vertices. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealRootRestriction
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
open RootedRestriction RepresentedRootRestriction
variable {n e:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K]
variable [LinearOrder K] [IsStrictOrderedRing K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def connectedSubmatrixToRoot (M:Matrix C C K) (hs:∀i j,M i j=M j i) (w:C→K)
    (X:Set C) (hX:ColorClosed M X) :
    Reduction (FixedRealComponents.connectedProblem basis
      (fun _:Fin 1=>fun i j:X=>M i.val j.val) (fun i:Fin 0=>i.elim0) (fun i:X=>w i.val))
      (RepresentedRootRestriction.rootProblem (presentation basis) M w X) := by
  apply queryReduction (presentation basis) MixedCode.encoding RootedCodeMachines.inputEncoding MixedCode.normalizer
    (FixedRealComponents.connectedValid (b:=1) (u:=0)) RepresentedRootRestriction.inputValid
    (totalEvaluation (fun _:Fin 1=>fun i j:X=>M i.val j.val) (fun i:Fin 0=>i.elim0) (fun i:X=>w i.val))
    (RepresentedRootRestriction.rootValue M w X) (fun g=>(0,g))
    ((fp_const _ _ 0).pair (fp_id _))
  · intro g hg
    exact ⟨hg.1,hg.2.2⟩
  · intro g hg
    change RepresentedRootRestriction.rootValue M w X (0,g)=_
    rw [RepresentedRootRestriction.rootValue,dif_pos hg.1.1,dif_pos hg.2.2,
      rootRestricted_eq_submatrix g hg.1.1 hg.2.1 ⟨0,hg.2.2⟩ M hs w X hX,
      totalEvaluation_valid _ _ _ _ hg.1.1,evaluate_homogeneous]

def submatrixReduction (M:Matrix C C K) (hs:∀i j,M i j=M j i) (w:C→K) (hw:∀i,0 < w i)
    (X:Set C) (hX:ColorClosed M X) :
    Reduction (FixedRealComponents.problem basis
      (fun _:Fin 1=>fun i j:X=>M i.val j.val) (fun i:Fin 0=>i.elim0) (fun i:X=>w i.val))
      (RepresentedRootRestriction.sourceProblem (presentation basis) M w) :=
  ((FixedRealComponents.componentReduction basis
    (fun _:Fin 1=>fun i j:X=>M i.val j.val) (fun i:Fin 0=>i.elim0) (fun i:X=>w i.val)).trans
      (connectedSubmatrixToRoot basis M hs w X hX)).trans (corollaryA2_root basis M w hw X)

def supportComponentReduction (M:Matrix C C K) (hs:∀i j,M i j=M j i) (w:C→K) (hw:∀i,0 < w i)
    (c:(colorSupport M hs).ConnectedComponent) :
    Reduction (FixedRealComponents.problem basis
      (fun _:Fin 1=>fun i j:c.supp=>M i.val j.val) (fun i:Fin 0=>i.elim0) (fun i:c.supp=>w i.val))
      (RepresentedRootRestriction.sourceProblem (presentation basis) M w) :=
  submatrixReduction basis M hs w hw c.supp (component_colorClosed M hs c)

end PlanarHom.FixedRealRootRestriction
