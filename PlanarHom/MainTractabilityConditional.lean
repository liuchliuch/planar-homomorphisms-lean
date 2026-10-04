import PlanarHom.TractableBlockFormsConditional
import PlanarHom.WeightedBlockTractabilityQuotientConditional
import PlanarHom.PositiveRealCoreClassObstruction

/-! NEW complete original-scope easy implications of main 1.1 and 1.3, with
only primitive positive Ising FP explicit. The ordinary raw input codec,
connected-component processing, empty inputs and actual weighted quotient are
handled by the compiled source programs. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Structures
variable {q : ℕ}

theorem nonnegative_class_inFP_of_ising
    (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (h : NonnegativeClass (L.matrices 0)) : L.problem.InFP := by
  have hs := h.symmetric
  obtain ⟨t,block,honto,hzero,hform⟩ := h
  exact L.proposition26_of_ising hIsing hunit hs block hzero
    (fun r=>PositiveRealCore.allowedBlock_form _ (hform r))

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
