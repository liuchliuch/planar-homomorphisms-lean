import PlanarHom.MainStructuralDichotomyAssemblyConditional
import PlanarHom.RectangularUnweightedSourceCompleteConditional

/-! Conditional assembly of Theorem 1.1 for fixed symmetric nonnegative algebraic
interactions. Rectangular classification supplies the final assembly argument;
`MainDichotomiesClosed` instantiates the explicit Potts and Ising parameters. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures
variable {q : ℕ}

/-- Literal support-component necessity on the original unweighted source.
No normalization, distinct-row, connectedness, or nonzero-matrix hypothesis is
imposed on the original interaction. -/
theorem nonnegative_class_of_not_hard_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hnot : ¬PromisedSharpPHard L.problem) :
    NonnegativeClass (L.matrices 0) :=
  L.main_nonnegative_class_of_rectangular_source_of_potts hPotts
    (RectangularUnweightedSourceForms.source_language_form_of_not_hard_of_potts hPotts) hunit hs hnn hnot

/-- Main Theorem1.1: the literal positive rank-one/tensor, bipartite
rank-two/tensor, and singleton-zero direct sums are in FP; every other fixed
symmetric nonnegative algebraic interaction is #P-hard. Both conclusions use
the original raw planar multigraph source and exact finite-field output codec. -/
theorem theorem11_of_potts_ising (hPotts : PositivePottsFoundation)
    (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (L : RealLanguage q 1 0)
    (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) :
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
      (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem) := by
  refine ⟨L.nonnegative_class_inFP_of_ising hIsing hunit,?_⟩
  intro hbad
  by_contra hnot
  exact hbad (L.nonnegative_class_of_not_hard_of_potts hPotts hunit hs hnn hnot)

/-- The conditional complexity alternative, including empty color sets and
zero interactions rather than silently deleting them from the source. -/
theorem theorem11_dichotomy_of_potts_ising (hPotts : PositivePottsFoundation)
    (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (L : RealLanguage q 1 0)
    (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) :
    L.problem.InFP ∨ PromisedSharpPHard L.problem := by
  classical
  by_cases h:NonnegativeClass (L.matrices 0)
  · exact Or.inl ((L.theorem11_of_potts_ising hPotts hIsing hunit hs hnn).1 h)
  · exact Or.inr ((L.theorem11_of_potts_ising hPotts hIsing hunit hs hnn).2 h)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
