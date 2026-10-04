import PlanarHom.SignedThreeReducibleAlgebra

/-! The literal Theorem 2.3 signed real structural alternatives. This predicate
contains no complexity assumptions, solver witnesses or nonnegativity clause. -/
noncomputable section
namespace PlanarHom.SignedThreeState

def ThreeStateEasy (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  M.rank≤1 ∨
    (∃a b c t:ℝ,BooleanEasy a b c ∧ ∃e:Equiv.Perm (Fin 3),
      ∀i j,M i j=blockMatrix a b c t (e i) (e j)) ∨
    PermutedStar M

end PlanarHom.SignedThreeState
