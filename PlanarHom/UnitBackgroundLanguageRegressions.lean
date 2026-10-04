import PlanarHom.ContextualGadgetClosure
import PlanarHom.RectangularNormalizationMomentSource

noncomputable section
namespace PlanarHom.UnitBackgroundLanguageRegressions
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode

variable {q bt : ℕ} (M : Fin bt → Matrix (Fin q) (Fin q) ℝ)
    (hM : ∀ l i j, IsAlgebraic ℚ (M l i j))

theorem matrices_unchanged : (unitLanguage M hM).matrices = M := rfl

theorem unit_weights : (unitLanguage M hM).weights = fun _ => 1 := rfl

theorem no_unary_labels : (unitLanguage M hM).unaries = fun l : Fin 0 => l.elim0 := rfl

/-- Empty color sets are permitted; no hidden nonempty condition is introduced. -/
def empty_colors : RealLanguage 0 bt 0 :=
  unitLanguage (fun _ i _ => i.elim0) (fun _ i _ => i.elim0)

/-- Empty matrix families are permitted independently of the color count. -/
def empty_labels : RealLanguage q 0 0 :=
  unitLanguage (fun l => l.elim0) (fun l => l.elim0)

/-- The exact field-presentation call shape from the whole original UnitCoreSource
consumer works using definitional matrix/unary/background equalities. -/
def original_presentation_call {K : IntermediateField ℚ ℝ} {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K)
    (A : Fin bt → Matrix (Fin q) (Fin q) K)
    (hA : ∀ l i j, IsAlgebraic ℚ (A l i j : ℝ)) :
    PromisePolyTimeTuringReduction
      (unitLanguage (fun l i j => (A l i j : ℝ)) hA).problem
      (evaluationProblem basis A (fun l : Fin 0 => l.elim0) (fun _ => 1)) :=
  (unitLanguage (fun l i j => (A l i j : ℝ)) hA).presentationDescentReduction
    K basis A (fun l : Fin 0 => l.elim0) (fun _ => 1)
    (fun _ _ _ => rfl) (fun l => l.elim0) (fun _ => rfl)

#check RectangularBackgroundSourceNormSimulation.exists_rectangular_quotient_moment_sources

end PlanarHom.UnitBackgroundLanguageRegressions
