import PlanarHom.NonnegativeSupportShapesBasic
import PlanarHom.NonbasicSupportHardness

-- Recovered original source theorem body; pure shape definitions are imported
-- from the checked extraction to avoid duplicate declarations.
noncomputable section
open Classical
set_option autoImplicit false
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity RootedRestriction NonnegativeSupportShapes
variable {q : ℕ}

theorem nonnegative_support_shapes_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hnn : ∀ i j,0≤L.matrices 0 i j) (hw : ∀ i,0<L.weights i)
    (hnot : ¬PromisedSharpPHard L.problem) :
    ∀ c : (colorSupport (L.matrices 0) hs).ConnectedComponent,
      Shape (fun i j : c.supp=>L.matrices 0 i.val j.val) := by
  have hb := L.numerical_support_basic_of_not_hard hPotts hs hw hnot
  intro c
  exact shape_of_basic_support _ (fun i j=>hs _ _) (fun i j=>hnn _ _) (hb c)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
