import PlanarHom.PositivePottsInterface
import PlanarHom.PottsCoefficientReduction

/-! NEW exact identity of the rational ordinary-input Potts problems used by
the radial compiler and the structural-classification foundation. This is
codec/field plumbing only and introduces no hardness premise or witness. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.PositivePottsProblemBridge
open Complexity AlgebraicProductInterpolation.RealLanguage ProperColoringPottsReduction

theorem rational_problem_eq (q : ℕ) :
    pottsProblem rationalBasis q=pottsRationalProblem q := rfl

def coefficient_reduction (q : ℕ) (hq : 0<q) :
    PromisePolyTimeTuringReduction (PottsCoefficientReduction.problem q) (pottsRationalProblem q) := by
  simpa only [PottsCoefficientPrograms.basis,rational_problem_eq] using
    PottsCoefficientReduction.reduction q hq

/-- Actual compiled conversion into every fixed finite real number field,
with the source graph promise and the literal I+J matrix unchanged. -/
def coefficient_field_reduction {K : IntermediateField ℚ ℝ} {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ) (hq : 0<q) :
    PromisePolyTimeTuringReduction (PottsCoefficientReduction.problem q)
      (FullLogarithmicPottsReduction.pottsProblem basis q) :=
  (coefficient_reduction q hq).trans (pottsFieldReduction basis q)

end PlanarHom.PositivePottsProblemBridge
