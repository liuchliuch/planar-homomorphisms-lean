import PlanarHom.PositiveUnaryRationalPowers

/-!
# Actual rational-power unary data inside one fixed finite field

This transports the proved real product identities through the injective field
embedding. The resulting source and target unaries are genuine elements of the
same finite intermediate field, suitable for the abstract-field reduction APIs.
-/

noncomputable section
namespace PlanarHom.ProductCompatibility
variable {I K L : Type} [Field K] [Field L]

/-- Ring embeddings preserve the actual finite numerical products. -/
theorem map_product (φ : K →+* L) (A : I → K) (xs : List I) :
    φ ((xs.map A).prod) = (xs.map (fun i => φ (A i))).prod := by
  rw [map_list_prod, List.map_map]
  rfl

/-- Product compatibility checked in a containing field descends to the
original field because its embedding is injective. -/
theorem compatible_of_field_embedding (φ : K →+* L) (A B : I → K)
    (h : Compatible (fun i => φ (A i)) (fun i => φ (B i))) : Compatible A B := by
  intro xs ys hlen hxs hys heq
  apply φ.injective
  rw [map_product, map_product]
  apply h xs ys hlen
  · exact fun i hi => (map_ne_zero φ).mpr (hxs i hi)
  · exact fun i hi => (map_ne_zero φ).mpr (hys i hi)
  · rw [← map_product, ← map_product, heq]

end PlanarHom.ProductCompatibility

namespace PlanarHom.PositiveUnaryRationalPowers
open ProductCompatibility
variable {I : Type}

/-- All genuine powered unary data can be placed in one fixed finite extension,
including the exact product-map and source-zero hypotheses used by the machines.
The original finite algebraic constant set is retained in that same field. -/
theorem exists_fixed_field_unary_data [Finite I] (u : I → ℝ) (hpos : ∀ i, 0 < u i)
    (hAlg : ∀ i, IsAlgebraic ℚ (u i)) (r : ℚ) (S : Set ℝ) (hS : S.Finite)
    (hSAlg : ∀ x ∈ S, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧ S ⊆ K ∧
      ∃ uK vK : I → K,
        (∀ i, (uK i : ℝ) = u i) ∧ (∀ i, (vK i : ℝ) = powered u r i) ∧
        (∀ i, uK i = 0 → vK i = 0) ∧
        Compatible uK vK ∧ HasProductMaps uK vK := by
  obtain ⟨K, hdim, hSK, hmem⟩ := exists_fixed_finite_extension u hpos hAlg r S hS hSAlg
  let uK : I → K := fun i => ⟨u i, (hmem i).1⟩
  let vK : I → K := fun i => ⟨powered u r i, (hmem i).2⟩
  have hcompat : Compatible uK vK := by
    apply compatible_of_field_embedding K.val.toRingHom
    change Compatible u (powered u r)
    exact compatible_real_rpow u hpos r
  refine ⟨K, hdim, hSK, uK, vK, fun _ => rfl, fun _ => rfl, ?_, hcompat,
    hasProductMaps_of_compatible uK vK hcompat⟩
  intro i hz
  have hz' : u i = 0 := congrArg (fun x : K => (x : ℝ)) hz
  exact ((ne_of_gt (hpos i)) hz').elim

end PlanarHom.PositiveUnaryRationalPowers
