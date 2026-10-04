import PlanarHom.PositiveUnaryPowerField

/-!
# Fixed rational-power extension of an already specified source field

The original source field is retained as an actual subfield of a fixed finite
compositum. This field depends only on the original field, fixed unary and fixed
rational exponent. No input-dependent sampling field or variable-field compositum
is used, and no equality of encodings in different bases is asserted.
-/

noncomputable section
namespace PlanarHom.PositiveUnaryRationalPowers
open ProductCompatibility
variable {I : Type}

/-- Preserve the entire specified finite source field while adjoining the fixed
actual rational-power unary values. -/
theorem exists_fixed_overfield_unary_data [Finite I]
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (u : I → ℝ) (hpos : ∀ i, 0 < u i) (hAlg : ∀ i, IsAlgebraic ℚ (u i)) (r : ℚ) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ K₀ ≤ K ∧
      ∃ uK vK : I → K,
        (∀ i, (uK i : ℝ) = u i) ∧ (∀ i, (vK i : ℝ) = powered u r i) ∧
        (∀ i, uK i = 0 → vK i = 0) ∧
        Compatible uK vK ∧ HasProductMaps uK vK := by
  obtain ⟨F, hF, _, hmem⟩ := exists_fixed_finite_extension u hpos hAlg r ∅ Set.finite_empty
    (by simp)
  letI : FiniteDimensional ℚ F := hF
  let K : IntermediateField ℚ ℝ := K₀ ⊔ F
  have hK : FiniteDimensional ℚ K := inferInstance
  have h₀ : K₀ ≤ K := le_sup_left
  have hF' : F ≤ K := le_sup_right
  let uK : I → K := fun i => ⟨u i, hF' (hmem i).1⟩
  let vK : I → K := fun i => ⟨powered u r i, hF' (hmem i).2⟩
  have hcompat : Compatible uK vK := by
    apply compatible_of_field_embedding K.val.toRingHom
    change Compatible u (powered u r)
    exact compatible_real_rpow u hpos r
  refine ⟨K, hK, h₀, uK, vK, fun _ => rfl, fun _ => rfl, ?_, hcompat,
    hasProductMaps_of_compatible uK vK hcompat⟩
  intro i hz
  have hz' : u i = 0 := congrArg (fun x : K => (x : ℝ)) hz
  exact ((ne_of_gt (hpos i)) hz').elim

/-- When the unary is already given in the prescribed source field, its lift is
exactly the canonical inclusion of that field. The source entries are not
replaced by unrelated representatives in a new field. -/
theorem exists_fixed_power_overfield [Finite I]
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (u : I → K₀) (hpos : ∀ i, 0 < (u i : ℝ)) (r : ℚ) :
    ∃ (K : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ K), FiniteDimensional ℚ K ∧
      ∃ vK : I → K,
        (∀ i, (vK i : ℝ) = (u i : ℝ) ^ (r : ℝ)) ∧
        (∀ i, IntermediateField.inclusion h₀ (u i) = 0 → vK i = 0) ∧
        Compatible (fun i => IntermediateField.inclusion h₀ (u i)) vK ∧
        HasProductMaps (fun i => IntermediateField.inclusion h₀ (u i)) vK := by
  have hAlg : ∀ i, IsAlgebraic ℚ (u i : ℝ) := fun i =>
    IsAlgebraic.algHom K₀.val (Algebra.IsAlgebraic.isAlgebraic (u i))
  obtain ⟨K, hK, h₀, uK, vK, hu, hv, hzero, hcompat, hmaps⟩ :=
    exists_fixed_overfield_unary_data K₀ (fun i => (u i : ℝ)) hpos hAlg r
  have hlu : uK = fun i => IntermediateField.inclusion h₀ (u i) := by
    funext i
    apply Subtype.ext
    exact hu i
  refine ⟨K, h₀, hK, vK, hv, ?_, ?_, ?_⟩
  · simpa only [hlu] using hzero
  · simpa only [hlu] using hcompat
  · simpa only [hlu] using hmaps

end PlanarHom.PositiveUnaryRationalPowers
