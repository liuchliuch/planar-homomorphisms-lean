import PlanarHom.RectangularCoreSourceEntranceConditional

noncomputable section
namespace PlanarHom.CommonCubeConditionalRegressions
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open ClosedMatrixFamily TypedBipartiteContext

/-- The actual structure still forces an exact power-of-two color count. -/
example {q : ℕ} {S : Set (Matrix (Fin q) (Fin q) ℝ)} (W : CommonCubeChart S) :
    q=2^W.dimension := W.cardinality

/-- All closure and availability conditions remain source-facing; only the
positive Potts foundation is passed as a parameter at this intermediate layer. -/
example {q : ℕ} (hPotts : PositivePottsFoundation)
    (S : Set (Matrix (Fin q) (Fin q) ℝ)) (hA : AlgebraicSourceClosed S)
    (htransfer : EffectiveSpectralClosed S) (hgadget : MixedPlanarGadgetClosed S)
    (P : PromiseProblem)
    (havail : ∀ N,∀ hN : N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hne : ∃ H,Admissible S H) (hnot : ¬PromisedSharpPHard P) :
    Nonempty (CommonCubeChart S) :=
  exists_common_cube_chart hPotts S hA htransfer hgadget P havail hne hnot

end PlanarHom.CommonCubeConditionalRegressions
