import PlanarHom.AlgebraicLanguagePresentation

/-! NEW transparent constructor inferred from the complete surviving UnitCoreSource
consumer. This is not recovered original code and supplies no gadget-closure
or source-availability theorem. The matrix family and unit weights are literal. -/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage

/-- The given real-algebraic matrix family with no unary labels and unit background. -/
def unitLanguage {q bt : ℕ}
    (M : Fin bt → Matrix (Fin q) (Fin q) ℝ)
    (hM : ∀ l i j, IsAlgebraic ℚ (M l i j)) : RealLanguage q bt 0 where
  matrices := M
  unaries := fun l => l.elim0
  weights := fun _ => 1
  matrices_algebraic := hM
  unaries_algebraic := fun l => l.elim0
  weights_algebraic := fun _ => isAlgebraic_one

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
