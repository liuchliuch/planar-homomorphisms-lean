import PlanarHom.MainDichotomiesClosed
import PlanarHom.FullLogarithmicPottsReduction
import PlanarHom.RectangularCoreSourceRigidityConditional
import PlanarHom.PositiveClassMomentSourceRigidity
import PlanarHom.TractableBlockFormsConditional
import PlanarHom.AvailableCommonCubeChart
import PlanarHom.CommonCubeChartBasicConsequences

/-! NEW source-facing body wrappers with both independent foundations proved. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Boolean BooleanTensorEasyAssembly

theorem lemma311 {q bt ut : ℕ} (L : RealLanguage q bt ut) (hunit : ∀i,L.weights i=1)
    (old : Fin bt) (hq : 3≤q) (hpd : (L.matrices old).PosDef)
    (hnn : ∀i j,0≤L.matrices old i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices old) hpd.1).Connected)
    (hfull : ∀i j,i≠j → EntropyCompletion.matrixLog (L.matrices old) i j≠0)
    (P : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem P) :
    PromisedSharpPHard P :=
  (positivePottsField_hard positivePottsFoundation L.basis q hq).trans
    (L.lemma311_potts_reduction hunit old hq hpd hnn hconn hfull P available)

theorem lemma311_source {q bt ut : ℕ} (L : RealLanguage q bt ut) (hunit : ∀i,L.weights i=1)
    (old : Fin bt) (hq : 3≤q) (hpd : (L.matrices old).PosDef)
    (hnn : ∀i j,0≤L.matrices old i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport (L.matrices old) hpd.1).Connected)
    (hfull : ∀i j,i≠j → EntropyCompletion.matrixLog (L.matrices old) i j≠0) :
    PromisedSharpPHard L.problem := by
  obtain ⟨p,hp⟩:=MixedCode.evaluationProblem_output_bound L.basis L.matricesK L.unariesK L.weightsK
  exact L.lemma311 hunit old hq hpd hnn hconn hfull L.problem
    (PromisePolyTimeTuringReduction.refl_of_output_bound L.problem p hp)

theorem theorem81 {q : ℕ} [Nonempty (Fin q)]
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (hpos : ∀i j,0<L.matrices 0 i j) :
    (PositiveTensorForm (L.matrices 0) → L.problem.InFP) ∧
    (¬PositiveTensorForm (L.matrices 0) → PromisedSharpPHard L.problem) :=
  L.theorem81_of_potts_ising positivePottsFoundation positiveIsingFoundation hunit hs hpos

theorem lemma82 {q : ℕ} [Nonempty (Fin q)]
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hpos : ∀i j,0<L.matrices 0 i j) (hdiag : ∀i,L.matrices 0 i i=1)
    (hinj : Function.Injective (L.matrices 0)) :
    PromisedSharpPHard L.problem ∨
      ∃d : ℕ,∃e : Fin q≃Cube d,∃ρ : Fin d→ℝ,
        (∀r,0<ρ r ∧ ρ r≠1) ∧ Matrix.reindex e e (L.matrices 0)=tensor ρ ∧ IsUnit (L.matrices 0) := by
  by_cases hh : PromisedSharpPHard L.problem
  · exact Or.inl hh
  · exact Or.inr (L.homogeneous_unit_diagonal_tensor_of_not_hard positivePottsFoundation hunit hs hpos hdiag hinj hh)

theorem proposition26 {q r : ℕ} (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i) (block : Fin q→Fin r)
    (hzero : ∀i j,block i≠block j → L.matrices 0 i j=0)
    (hform : ∀b : Fin r,TractableBlockComposition.Form
      (fun i j : {i // block i=b}=>L.matrices 0 i.val j.val)) : L.problem.InFP :=
  L.proposition26_of_ising positiveIsingFoundation hunit hs block hzero hform

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
namespace PlanarHom.RectangularCoreSourceRigidity
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open RectangularSourceNormSimulation

theorem proposition92 {x y : ℕ} [Nonempty (Fin x)] [Nonempty (Fin y)]
    (L : RealLanguage (x+y) 1 0) (hunit : ∀i,L.weights i=1)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀i j,0<B i j) (hM : L.matrices 0=block B)
    (hrows : ∀i j,i≠j → ∀t : ℝ,B i≠t•B j)
    (hcolumns : ∀i j,i≠j → ∀t : ℝ,B.transpose i≠t•B.transpose j) :
    PromisedSharpPHard L.problem ∨
      ∃d : ℕ,x=2^d ∧ y=2^d ∧ ∃eX : Fin x≃Boolean.Cube d,∃eY : Fin y≃Boolean.Cube d,
        ∃γ : ℝ,∃ρ : Fin d→ℝ,0<γ ∧ (∀i,0<ρ i ∧ ρ i<1) ∧
        ∀i j,B i j=γ*Boolean.tensor ρ (eX i) (eY j) :=
  proposition92_of_potts positivePottsFoundation L hunit B hB hM hrows hcolumns

end PlanarHom.RectangularCoreSourceRigidity
