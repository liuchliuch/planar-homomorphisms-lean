import PlanarHom.FixedRealSignedJointExtrema

/-! NEW full fixed-real A.7 endpoints, including simultaneous retention of
all original labels and both attained extreme-magnitude masks. -/
noncomputable section
namespace PlanarHom.FixedRealSignedTransforms
open DensePolynomial FixedRealExtension Complexity RepresentedBit FiniteLanguageAliases
variable {n e q b u : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]

 theorem theoremA7_all_five (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) (selected : Fin b)
    (hM : M selected ≠ 0) (base : Problem)
    (available : Reduction (FixedRealMixedInterpolation.problem basis M U w) base) :
    ∃a z : ℝ, 0 < a ∧ 0 < z ∧
      (∃i j, |φ (M selected i j)| = a) ∧ (∃i j, |φ (M selected i j)| = z) ∧
      (∀i j, M selected i j ≠ 0 → a ≤ |φ (M selected i j)|) ∧
      (∀i j, |φ (M selected i j)| ≤ z) ∧
      Nonempty (Reduction (FixedRealMixedInterpolation.problem basis
        (appendFamily (appendFamily M (transform φ (M selected)))
          (extremalTransforms φ (M selected) a z)) U w) base) := by
  obtain ⟨a,z,ha,hz,ham,hzm,hmin,hmax⟩ := attained_extrema φ (M selected) hM
  refine ⟨a,z,ha,hz,ham,hzm,hmin,hmax,?_⟩
  have first := withOriginalReduction basis φ M U w selected base available
  have second := extremaWithOriginalReduction basis φ
    (appendFamily M (transform φ (M selected))) U w (Fin.castAdd 3 selected)
    a z ha hz (by simpa only [appendFamily_old] using hmin)
    (by simpa only [appendFamily_old] using hmax) base first
  exact ⟨by simpa only [appendFamily_old] using second⟩

/-- The support-magnitude-source chain uses the same prescribed presentation
and retains the literal original background and all ordinary unary factors. -/
theorem theoremA7_chain (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (φ : K →+* ℝ) (M : Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K) :
    Nonempty (Reduction (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => support (M i j)) U w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => magnitude φ (M i j)) U w)) ∧
    Nonempty (Reduction (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => fun i j => magnitude φ (M i j)) U w)
      (FixedRealMixedInterpolation.problem basis (fun _ : Fin 1 => M) U w)) :=
  ⟨⟨supportMagnitudeReduction basis φ M U w⟩,⟨magnitudeReduction φ basis M U w⟩⟩

end PlanarHom.FixedRealSignedTransforms
