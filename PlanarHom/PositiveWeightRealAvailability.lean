import PlanarHom.PositiveWeightRemovalReduction
import PlanarHom.AlgebraicProductInterpolation

/-! Source-facing weighted-background removal with the literal real-algebraic
source language. This module covers the inverse diagonal and weight-removal
clauses of3.7; the rational diagonal/unary closure is a separate obligation. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases PositiveWeightRemoval
variable {q bt ut : ℕ} (L : RealLanguage q bt ut)

def inverseWeightProblem : PromiseProblem :=
  evaluationProblem L.basis (appendOne L.matricesK (Matrix.diagonal (fun i=>(L.weightsK i)⁻¹)))
    L.unariesK L.weightsK

def unitWeightProblem : PromiseProblem :=
  evaluationProblem L.basis L.matricesK L.unariesK (fun _=>1)

/-- Joint inverse-diagonal availability retains the original source field,
all binary/unary labels and every background weight. -/
def lemma37_inverseDiagonal (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀ i,0<L.weights i) (hnonzero : ∀ i,L.matrices old i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction L.inverseWeightProblem base :=
  (inverseDiagonalFromRows L.basis L.matricesK L.unariesK L.weightsK old hs hw hnonzero hproj).trans available

/-- The full finite-language background-removal implication, including the
single-matrix case, composes with the same original supplied availability. -/
def lemma37_removeWeights (old : Fin bt)
    (hs : ∀ i j,L.matrices old i j=L.matrices old j i)
    (hw : ∀ i,0<L.weights i) (hnonzero : ∀ i,L.matrices old i≠0)
    (hproj : ∀ i j,i≠j→∀t:ℝ,L.matrices old i≠t • L.matrices old j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction L.unitWeightProblem base :=
  (removePositiveWeights L.basis L.matricesK L.unariesK L.weightsK old hs hw hnonzero hproj).trans available

/-- The new field diagonal is exactly the source's real D inverse. -/
theorem inverseWeightMatrix_real :
    (Matrix.diagonal (fun i=>(L.weightsK i)⁻¹)).map L.field.val =
      Matrix.diagonal (fun i=>(L.weights i)⁻¹) := by
  ext i j
  by_cases h : i=j <;> simp [Matrix.diagonal_apply,h]
  rfl

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
