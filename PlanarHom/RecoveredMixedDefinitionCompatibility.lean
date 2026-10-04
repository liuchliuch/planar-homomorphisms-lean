import PlanarHom.TypedMixedPhysicalAvailabilityTransport

/-! NEW compatibility checks for the only mechanically extracted duplicate
recovered definitions. These equations close by definitional equality. -/
noncomputable section
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteSpectral RectangularMixedGadgets
variable {x y s : ℕ} {R : Type} [Field R]

example (B : Matrix (Fin x) (Fin y) R) : crossFin B =
    Matrix.reindex finSumFinEquiv finSumFinEquiv (cross B) := rfl

example (K : Matrix (Fin y) (Fin y) R) : onYFin (x:=x) K =
    Matrix.reindex finSumFinEquiv finSumFinEquiv (onY (X:=Fin x) K) := rfl

example (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) : yFamily F FB =
    {N | N.IsHermitian ∧ TypedContextuallyAvailable (domains x y) F FB (onYFin N) sameY} := rfl

end PlanarHom.TypedBipartiteContext
