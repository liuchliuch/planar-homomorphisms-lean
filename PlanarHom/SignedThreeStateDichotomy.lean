import PlanarHom.SignedThreeEasyClosure
import PlanarHom.SignedThreeHardComplement

/-! Theorem 2.3 with its complete signed structural scope in the main-text
algebraic bit model. Both implications are unconditional. The cited extension
to arbitrary fixed real coefficient fields is deliberately left to Appendix A;
no finite-dimensional-over-Q hypothesis is silently claimed for all reals. -/
noncomputable section
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode BooleanTensorFPClosure AlgebraicProductInterpolation

/-- Original algebraic source-language version of the complete signed
three-state classification, retaining the literal rank and block alternatives. -/
theorem theorem23_algebraic (L : RealLanguage 3 1 0)
    (hunit : ∀i,L.weights i=1) (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) :
    (ThreeStateEasy (L.matrices 0)→L.problem.InFP) ∧
    (¬ThreeStateEasy (L.matrices 0)→PromisedSharpPHard L.problem) := by
  have hsF : ∀i j,L.matricesK 0 i j=L.matricesK 0 j i :=
    fun i j=>Subtype.ext (hs i j)
  have hm : L.matricesK=(fun _:Fin 1=>L.matricesK 0) := by
    funext l
    exact congrArg L.matricesK (Subsingleton.elim _ _)
  have hu : L.unariesK=(emptyUnaries : Fin 0→Fin 3→L.field) := by
    funext l
    exact l.elim0
  have hw : L.weightsK=(fun _=>1) := by
    funext i
    exact Subtype.ext (hunit i)
  constructor
  · intro h
    change (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK).InFP
    rw [hm,hu,hw]
    exact signed_three_easy_inFP L.basis (L.matricesK 0) hsF h
  · intro h
    change PromisedSharpPHard (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK)
    rw [hm,hu,hw]
    exact signed_three_hard L.basis (L.matricesK 0) hsF h

/-- The exact algebraic scope is explicit at the public endpoint. -/
def Theorem23AlgebraicStatement : Prop :=
  ∀L:RealLanguage 3 1 0,(∀i,L.weights i=1)→
    (∀i j,L.matrices 0 i j=L.matrices 0 j i)→
    (ThreeStateEasy (L.matrices 0)→L.problem.InFP) ∧
    (¬ThreeStateEasy (L.matrices 0)→PromisedSharpPHard L.problem)

theorem theorem23AlgebraicStatement : Theorem23AlgebraicStatement := theorem23_algebraic

end PlanarHom.SignedThreeState
