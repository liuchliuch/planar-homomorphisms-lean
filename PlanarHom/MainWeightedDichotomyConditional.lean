import PlanarHom.MainWeightedDichotomyAssemblyConditional
import PlanarHom.BipartiteWeightedSourceCompleteConditional

/-! Conditional assembly of Theorem 1.3 using the proved rectangular theorem.
`MainDichotomiesClosed` instantiates the remaining foundation parameters. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures
variable {q : ℕ}

/-- Necessity on the literal complete actual-row quotient, including its zero
class and original class-weight sums. No assumption is made on original twins. -/
theorem positive_vertex_weight_class_of_not_hard_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hw : ∀ i,0<L.weights i)
    (hnot : ¬PromisedSharpPHard L.problem) :
    PositiveVertexWeightClass (L.matrices 0) L.weights hs :=
  L.main_positive_vertex_weight_class_of_rectangular_source_of_potts hPotts
    (BipartiteWeightedSourceCanonical.allowedWeighted_of_not_hard_of_potts hPotts) hs hnn hw hnot

/-- Theorem1.3 in the exact algebraic bit model and the original source codec.
Disconnected supports, zero rows, repeated rows, loops and empty inputs are
included. The structural predicate performs the genuine row quotient first. -/
theorem theorem13_of_potts_ising (hPotts : PositivePottsFoundation)
    (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hw : ∀ i,0<L.weights i) :
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs → L.problem.InFP) ∧
      (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs → PromisedSharpPHard L.problem) := by
  refine ⟨L.positive_vertex_weight_class_inFP_of_ising hIsing hs,?_⟩
  intro hbad
  by_contra hnot
  exact hbad (L.positive_vertex_weight_class_of_not_hard_of_potts hPotts hs hnn hw hnot)

/-- The conditional complexity alternative for every original nonnegative
source with one fixed positive algebraic vertex-weight vector. -/
theorem theorem13_dichotomy_of_potts_ising (hPotts : PositivePottsFoundation)
    (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (L : RealLanguage q 1 0)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hw : ∀ i,0<L.weights i) :
    L.problem.InFP ∨ PromisedSharpPHard L.problem := by
  classical
  by_cases h:PositiveVertexWeightClass (L.matrices 0) L.weights hs
  · exact Or.inl ((L.theorem13_of_potts_ising hPotts hIsing hs hnn hw).1 h)
  · exact Or.inr ((L.theorem13_of_potts_ising hPotts hIsing hs hnn hw).2 h)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
