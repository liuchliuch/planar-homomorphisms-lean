import PlanarHom.Structures

/-! NEW literal zero-one component predicate inferred from the surviving
shape consumer and matching the three graph types in Theorem 7.1. This defines
the structural criterion only; it does not assert the complexity theorem. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.ZeroOneBasicStructure
variable {C : Type}

def BasicZeroOneComponent (A : Matrix C C ℝ) : Prop :=
  (Nonempty C ∧ ∀i j,A i j=1) ∨
  (∃ side : C → Bool, Function.Surjective side ∧ ∀i j,A i j=if side i=side j then 0 else 1) ∨
  (Nonempty C ∧ Subsingleton C ∧ A=0)

end PlanarHom.ZeroOneBasicStructure
