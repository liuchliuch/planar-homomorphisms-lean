import PlanarHom.FixedRealSignedTransforms

/-! NEW completion of A.7: all transforms coexist with the entire source
language. The least nonzero and greatest magnitude masks are attained fixed
constants and use the same exact charged interpolation machinery. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealSignedTransforms
open DensePolynomial FixedRealExtension Complexity Complexity.MixedCode RepresentedBit ProductCompatibility
open FiniteLanguageAliases
variable {n e q b u : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K) (φ : K →+* ℝ)

def withOriginalReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (selected : Fin b)
    (base : Problem) (available : Reduction (FixedRealMixedInterpolation.problem basis M U w) base) :
    Reduction (FixedRealMixedInterpolation.problem basis
      (appendFamily M (transform φ (M selected))) U w) base := by
  apply FixedRealMixedInterpolation.binaryFinite_joint basis M U w (transform φ (M selected))
    (fun _ => selected) _ _ base available
  · intro l i j h
    fin_cases l <;> simp [transform,support,magnitude,sign,h]
  · intro l
    fin_cases l
    · simpa [transform] using support_maps φ (fun p : Fin q × Fin q => M selected p.1 p.2)
    · simpa [transform] using magnitude_maps φ (fun p : Fin q × Fin q => M selected p.1 p.2)
    · simpa [transform] using sign_maps φ (fun p : Fin q × Fin q => M selected p.1 p.2)

def supportMagnitudeReduction (M : Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) :
    Reduction (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => support (M i j)) U w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => magnitude φ (M i j)) U w) := by
  have he : (fun _ : Fin 1 => fun i j => support (magnitude φ (M i j))) =
      (fun _ : Fin 1 => fun i j => support (M i j)) := by
    funext l i j
    have hz : magnitude φ (M i j) = 0 ↔ M i j = 0 := by
      rw [←map_eq_zero φ,magnitude_image,abs_eq_zero,map_eq_zero]
    simp only [support,hz]
  simpa only [he] using supportReduction φ basis (fun i j => magnitude φ (M i j)) U w

 theorem theoremA7_mixed_equivalence (M : Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) :
    Nonempty (Reduction (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w)
      (FixedRealMixedInterpolation.problem basis (mixed φ M) U w)) ∧
    Nonempty (Reduction (FixedRealMixedInterpolation.problem basis (mixed φ M) U w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w)) :=
  ⟨⟨reverseMixedReduction φ basis M U w⟩,⟨forwardMixedReduction φ basis M U w⟩⟩

 def magnitudeMask (A : K) (a : ℝ) : K := if |φ A| = a then 1 else 0

 @[simp] theorem magnitudeMask_image (A : K) (a : ℝ) :
    φ (magnitudeMask φ A a) = if |φ A| = a then 1 else 0 := by
  by_cases h : |φ A| = a <;> simp [magnitudeMask,h]

 theorem min_mask_maps {I : Type} (A : I → K) (a : ℝ) (ha : 0 < a)
    (hmin : ∀i, A i ≠ 0 → a ≤ |φ (A i)|) :
    HasProductMaps A (fun i => magnitudeMask φ (A i) a) := by
  apply hasProductMaps_of_compatible
  apply Compatible.of_injective_map φ
  simpa only [magnitudeMask_image,extremalMask] using
    compatible_min_magnitude_mask (fun i => φ (A i)) a ha
      (fun i hi => hmin i ((map_ne_zero φ).mp hi))

 theorem max_mask_maps {I : Type} (A : I → K) (a : ℝ) (ha : 0 < a)
    (hmax : ∀i, |φ (A i)| ≤ a) :
    HasProductMaps A (fun i => magnitudeMask φ (A i) a) := by
  apply hasProductMaps_of_compatible
  apply Compatible.of_injective_map φ
  simpa only [magnitudeMask_image,extremalMask] using
    compatible_max_magnitude_mask (fun i => φ (A i)) a ha hmax

 def extremalTransforms (M : Matrix (Fin q) (Fin q) K) (a z : ℝ) :
    Fin 2 → Matrix (Fin q) (Fin q) K :=
  fun l i j => magnitudeMask φ (M i j) (if l = 0 then a else z)

 def extremaWithOriginalReduction (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (selected : Fin b)
    (a z : ℝ) (ha : 0 < a) (hz : 0 < z)
    (hmin : ∀i j, M selected i j ≠ 0 → a ≤ |φ (M selected i j)|)
    (hmax : ∀i j, |φ (M selected i j)| ≤ z)
    (base : Problem) (available : Reduction (FixedRealMixedInterpolation.problem basis M U w) base) :
    Reduction (FixedRealMixedInterpolation.problem basis
      (appendFamily M (extremalTransforms φ (M selected) a z)) U w) base := by
  apply FixedRealMixedInterpolation.binaryFinite_joint basis M U w
    (extremalTransforms φ (M selected) a z) (fun _ => selected) _ _ base available
  · intro l i j h
    fin_cases l <;> simp [extremalTransforms,magnitudeMask,h,(ne_of_gt ha).symm,(ne_of_gt hz).symm]
  · intro l
    fin_cases l
    · simpa [extremalTransforms] using min_mask_maps φ (fun p : Fin q × Fin q => M selected p.1 p.2)
        a ha (fun p hp => hmin p.1 p.2 hp)
    · simpa [extremalTransforms] using max_mask_maps φ (fun p : Fin q × Fin q => M selected p.1 p.2)
        z hz (fun p => hmax p.1 p.2)

 theorem attained_extrema (M : Matrix (Fin q) (Fin q) K) (hM : M ≠ 0) :
    ∃a z : ℝ, 0 < a ∧ 0 < z ∧
      (∃i j, |φ (M i j)| = a) ∧ (∃i j, |φ (M i j)| = z) ∧
      (∀i j, M i j ≠ 0 → a ≤ |φ (M i j)|) ∧ (∀i j, |φ (M i j)| ≤ z) := by
  let S : Finset (Fin q × Fin q) := Finset.univ.filter (fun p => M p.1 p.2 ≠ 0)
  have hn : S.Nonempty := by
    by_contra h
    apply hM
    ext i j
    by_contra hij
    change M i j ≠ 0 at hij
    exact h ⟨(i,j),by simp [S,hij]⟩
  obtain ⟨lo,hlo,hmin⟩ := Finset.exists_min_image S (fun p => |φ (M p.1 p.2)|) hn
  obtain ⟨hi,hhi,hmax⟩ := Finset.exists_max_image S (fun p => |φ (M p.1 p.2)|) hn
  have hlo' : M lo.1 lo.2 ≠ 0 := (Finset.mem_filter.mp hlo).2
  have hhi' : M hi.1 hi.2 ≠ 0 := (Finset.mem_filter.mp hhi).2
  have ha := abs_pos.mpr ((map_ne_zero φ).mpr hlo')
  have hz := abs_pos.mpr ((map_ne_zero φ).mpr hhi')
  refine ⟨_,_,ha,hz,⟨lo.1,lo.2,rfl⟩,⟨hi.1,hi.2,rfl⟩,?_,?_⟩
  · intro i j hij
    exact hmin (i,j) (by simp [S,hij])
  · intro i j
    by_cases hij : M i j = 0
    · simpa [hij] using hz.le
    · exact hmax (i,j) (by simp [S,hij])

end PlanarHom.FixedRealSignedTransforms
