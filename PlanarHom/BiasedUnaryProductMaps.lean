import PlanarHom.BiasedBinaryPrimeProductMaps

/-! Distinct positive diagonal loop values give every Boolean unary by genuine
product interpolation. No leaf construction or extra spectral premise is used. -/
noncomputable section
namespace PlanarHom.BiasedPositiveHardness
open ProductCompatibility BiasedBinaryProductSeparation
variable {K : Type} [Field K]

theorem unary_product_maps (ι : K →+* ℝ) (a c : K)
    (ha : 0<ι a) (hc : 0<ι c) (hac : a≠c) (U : Bool → K) :
    HasProductMaps (bitWeight a c) U := by
  apply hasProductMaps_of_compatible
  intro xs ys hlen _ _ he
  change bitProduct xs a c=bitProduct ys a c at he
  have he' := congrArg ι he
  rw [bitProduct_eq,bitProduct_eq] at he'
  simp only [map_mul,map_pow] at he'
  have hne : ι a≠ι c := fun h => hac (ι.injective h)
  obtain ⟨h0,h1⟩ := two_product_counts (ι a) (ι c) ha hc hne
    (xs.count false) (xs.count true) (ys.count false) (ys.count true)
    (by simpa using hlen) he'
  have hu : U=bitWeight (U false) (U true) := by funext b; cases b <;> rfl
  rw [hu]
  change bitProduct xs (U false) (U true)=bitProduct ys (U false) (U true)
  rw [bitProduct_eq,bitProduct_eq,h0,h1]

theorem unary_product_maps_fin (ι : K →+* ℝ) (a c : K)
    (ha : 0<ι a) (hc : 0<ι c) (hac : a≠c) (U : Bool → K) :
    HasProductMaps (fun i : Fin 2 => bitWeight a c (finTwoEquiv i)) (fun i => U (finTwoEquiv i)) :=
  hasProductMaps_of_compatible _ _ ((compatible_of_hasProductMaps _ _
    (unary_product_maps ι a c ha hc hac U)).comp finTwoEquiv)

theorem binary_product_maps_fin (a b c x y z : K)
    (h : HasProductMaps (pairWeight a b c) (pairWeight x y z)) :
    HasProductMaps (fun p : Fin 2 × Fin 2 => pairWeight a b c (finTwoEquiv p.1,finTwoEquiv p.2))
      (fun p => pairWeight x y z (finTwoEquiv p.1,finTwoEquiv p.2)) :=
  hasProductMaps_of_compatible _ _ ((compatible_of_hasProductMaps _ _ h).comp
    (fun p : Fin 2 × Fin 2 => (finTwoEquiv p.1,finTwoEquiv p.2)))

end PlanarHom.BiasedPositiveHardness
