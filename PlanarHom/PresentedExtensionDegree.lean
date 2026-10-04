import PlanarHom.VariableFieldEffectiveTransfer
import Mathlib.LinearAlgebra.Dimension.Free

/-! The source's bounded relative degrees give exactly the bounded rational
coordinate dimensions used by the variable-field machine interface. -/
noncomputable section
namespace PlanarHom.EffectiveProductTransfer

/-- The fixed base-field degree is absorbed into the uniform constant. -/
theorem basis_dimension_le_of_relative_degree
    {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra K L] [Algebra ℚ L]
    [IsScalarTower ℚ K L] [FiniteDimensional ℚ K] [FiniteDimensional K L]
    {d c : ℕ} (b : Module.Basis (Fin d) ℚ L) (h : Module.finrank K L ≤ c) :
    d ≤ Module.finrank ℚ K * c := by
  have hd : Module.finrank ℚ L = d := by simpa using Module.finrank_eq_card_basis b
  calc
    d = Module.finrank ℚ L := hd.symm
    _ = Module.finrank ℚ K * Module.finrank K L := (Module.finrank_mul_finrank ℚ K L).symm
    _ ≤ Module.finrank ℚ K * c := Nat.mul_le_mul_left _ h

/-- Uniform form, without constructing a compositum of the target fields. -/
theorem exists_absolute_degree_bound_of_relative
    {X K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (L : X → Type) [∀ x, Field (L x)] [∀ x, Algebra K (L x)] [∀ x, Algebra ℚ (L x)]
    [∀ x, IsScalarTower ℚ K (L x)] [∀ x, FiniteDimensional K (L x)]
    (d : X → ℕ) (b : ∀ x, Module.Basis (Fin (d x)) ℚ (L x))
    (c : ℕ) (h : ∀ x, Module.finrank K (L x) ≤ c) :
    ∃ C : ℕ, ∀ x, d x ≤ C :=
  ⟨Module.finrank ℚ K*c, fun x => basis_dimension_le_of_relative_degree (b x) (h x)⟩

end PlanarHom.EffectiveProductTransfer
