import PlanarHom.SupportTransformCompatibility

/-! Exact original signed-source product compatibility for the two extremal
absolute-value masks, including source zeros and attained extrema. -/
noncomputable section
namespace PlanarHom.ProductCompatibility
variable {I : Type}

theorem Compatible.trans_nonzero {K : Type} [Field K] {A B C : I → K}
    (hAB : Compatible A B) (hBC : Compatible B C)
    (hB : ∀ i, A i ≠ 0 → B i ≠ 0) : Compatible A C := by
  intro xs ys hlen hxs hys heq
  exact hBC xs ys hlen (fun i hi => hB i (hxs i hi)) (fun i hi => hB i (hys i hi))
    (hAB xs ys hlen hxs hys heq)

theorem compatible_min_magnitude_mask (A : I → ℝ) (a : ℝ) (ha : 0 < a)
    (hmin : ∀ i, A i ≠ 0 → a ≤ |A i|) :
    Compatible A (extremalMask (fun i => |A i|) a) :=
  (compatible_abs A).trans_nonzero
    (compatible_lower_mask (fun i => |A i|) a ha (fun i hi => hmin i (abs_ne_zero.mp hi)))
    (fun _ hi => abs_ne_zero.mpr hi)

theorem compatible_max_magnitude_mask (A : I → ℝ) (b : ℝ) (hb : 0 < b)
    (hmax : ∀ i, |A i| ≤ b) :
    Compatible A (extremalMask (fun i => |A i|) b) :=
  (compatible_abs A).trans_nonzero
    (compatible_upper_mask (fun i => |A i|) b hb (fun i hi =>
      ⟨abs_pos.mpr (abs_ne_zero.mp hi), hmax i⟩)) (fun _ hi => abs_ne_zero.mpr hi)

theorem hasProductMaps_min_magnitude_mask (A : I → ℝ) (a : ℝ) (ha : 0 < a)
    (hmin : ∀ i, A i ≠ 0 → a ≤ |A i|) :
    HasProductMaps A (extremalMask (fun i => |A i|) a) :=
  hasProductMaps_of_compatible _ _ (compatible_min_magnitude_mask A a ha hmin)

theorem hasProductMaps_max_magnitude_mask (A : I → ℝ) (b : ℝ) (hb : 0 < b)
    (hmax : ∀ i, |A i| ≤ b) :
    HasProductMaps A (extremalMask (fun i => |A i|) b) :=
  hasProductMaps_of_compatible _ _ (compatible_max_magnitude_mask A b hb hmax)

end PlanarHom.ProductCompatibility
