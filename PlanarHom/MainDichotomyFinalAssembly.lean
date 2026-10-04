import PlanarHom.MainStructuralDichotomyConditional
import PlanarHom.MainWeightedDichotomyConditional
import PlanarHom.MainDichotomyScope
import PlanarHom.PositiveIsingFoundationClosed

/-! NEW final main-source assembly with the actual Ising proof instantiated.
All internal positive, rectangular, support and quotient dependencies are
proved. The single independently identified open premise is all-size positive
Potts hardness; it is not asserted here or replaced by a target classification. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures BooleanTensorEasyAssembly
variable {q : ℕ}

theorem nonnegative_class_inFP (L : RealLanguage q 1 0)
    (hunit : ∀i,L.weights i=1) (h : NonnegativeClass (L.matrices 0)) :
    L.problem.InFP := L.nonnegative_class_inFP_of_ising positiveIsingFoundation hunit h

theorem positive_vertex_weight_class_inFP (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h : PositiveVertexWeightClass (L.matrices 0) L.weights hs) :
    L.problem.InFP := L.positive_vertex_weight_class_inFP_of_ising positiveIsingFoundation hs h

theorem theorem11_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hunit : ∀i,L.weights i=1) (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) :
    (NonnegativeClass (L.matrices 0) → L.problem.InFP) ∧
    (¬NonnegativeClass (L.matrices 0) → PromisedSharpPHard L.problem) :=
  L.theorem11_of_potts_ising hPotts positiveIsingFoundation hunit hs hnn

theorem theorem13_of_potts (hPotts : PositivePottsFoundation) (L : RealLanguage q 1 0)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀i j,0≤L.matrices 0 i j) (hw : ∀i,0<L.weights i) :
    (PositiveVertexWeightClass (L.matrices 0) L.weights hs → L.problem.InFP) ∧
    (¬PositiveVertexWeightClass (L.matrices 0) L.weights hs → PromisedSharpPHard L.problem) :=
  L.theorem13_of_potts_ising hPotts positiveIsingFoundation hs hnn hw

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
namespace PlanarHom.MainDichotomyScope
open AlgebraicProductInterpolation.RealLanguage

theorem theorem11Statement_of_potts (hPotts : PositivePottsFoundation) : Theorem11Statement := by
  intro q L hunit hs hnn
  exact L.theorem11_of_potts hPotts hunit hs hnn

theorem theorem13Statement_of_potts (hPotts : PositivePottsFoundation) : Theorem13Statement := by
  intro q L hs hnn hw
  exact L.theorem13_of_potts hPotts hs hnn hw

end PlanarHom.MainDichotomyScope
