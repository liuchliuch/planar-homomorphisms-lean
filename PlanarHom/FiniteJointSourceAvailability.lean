import PlanarHom.UnitBackgroundLanguage

/-! Exact recovered finite joint source predicate, extracted into a narrow
independent module. This definition asserts no availability instance by itself.
It records actual finite-family source programs and retains the original type. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity
variable {q : ℕ}

/-- Genuine base-language joint availability. This must be proved by the
application's source compiler; singleton availability is not a substitute. -/
def FiniteJointSourceAvailable
    (S : Set (Matrix (Fin q) (Fin q) ℝ))
    (hS : ∀ M ∈ S, ∀ i j, IsAlgebraic ℚ (M i j)) (P : PromiseProblem) : Prop :=
  ∀ s, ∀ F : Fin s → Matrix (Fin q) (Fin q) ℝ, ∀ hF : ∀ l, F l ∈ S,
    Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage F (fun l => hS (F l) (hF l))).problem P)


end PlanarHom.AlgebraicProductInterpolation.RealLanguage
