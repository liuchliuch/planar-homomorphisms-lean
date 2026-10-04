import PlanarHom.AlgebraicProductOverfield
import PlanarHom.RealSpectralInterpolation

/-!
# One fixed overfield for genuine spectral interpolation

The original intermediate field remains the source field. We adjoin one fixed
finite alphabet containing the actual distinct spectral scalars, their target
values, the canonical whole-eigenspace projector entries, and the actual CFC
entries. The resulting basis presents this one overfield; it does not replace
the supplied source basis. All these choices depend only on the fixed matrix
and scalar function, never on a graph, exponent, or oracle query.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.SpectralFieldPresentation
open AlgebraicProductInterpolation ProductCompatibility

variable {K₀ : IntermediateField ℚ ℝ} {q : ℕ}

/-- The literal real image of the source matrix. -/
def realMatrix (C : Matrix (Fin q) (Fin q) K₀) : Matrix (Fin q) (Fin q) ℝ :=
  C.map K₀.val

/-- The number of distinct actual spectral values, including zero when present. -/
def spectralCount (C : Matrix (Fin q) (Fin q) K₀) : ℕ :=
  Nat.card (spectrum ℝ (realMatrix C))

/-- A finite index set for all fixed constants needed by spectral recovery. -/
abbrev ConstantIndex (C : Matrix (Fin q) (Fin q) K₀) :=
  Fin (spectralCount C) ⊕
    (Fin (spectralCount C) ⊕
      ((Fin (spectralCount C) × Fin q × Fin q) ⊕ (Fin q × Fin q)))

/-- Distinct eigenvalues, scalar target values, projectors, and the actual target matrix. -/
def constants (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) : ConstantIndex C → ℝ :=
  Sum.elim (RealSpectralInterpolation.scalar (realMatrix C))
    (Sum.elim (fun i => f (RealSpectralInterpolation.scalar (realMatrix C) i))
      (Sum.elim (fun p => RealSpectralInterpolation.projector (realMatrix C) p.1 p.2.1 p.2.2)
        (fun p => cfc f (realMatrix C) p.1 p.2)))

/-- One compositum retaining the whole original source field. -/
def field (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) : IntermediateField ℚ ℝ :=
  extensionField K₀ (constants C f)

theorem source_le_field (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) :
    K₀ ≤ field C f := le_sup_left

/-- The original source inclusion, with literal unchanged real values. -/
def inclusion (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) : K₀ →ₐ[ℚ] field C f :=
  sourceInclusion K₀ (constants C f)

@[simp] theorem inclusion_real (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) (x : K₀) :
    (inclusion C f x : ℝ) = x := rfl

/-- The lifted source matrix uses that same inclusion on every entry. -/
def sourceMatrix (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) :
    Matrix (Fin q) (Fin q) (field C f) := C.map (inclusion C f)

/-- Actual source spectral scalars in the common overfield. -/
def a (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) (i : Fin (spectralCount C)) : field C f :=
  targetValue K₀ (constants C f) (.inl i)

/-- Actual target spectral scalars in the common overfield. -/
def b (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) (i : Fin (spectralCount C)) : field C f :=
  targetValue K₀ (constants C f) (.inr (.inl i))

/-- Canonical whole-eigenspace projectors with entries in the common overfield. -/
def P (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) (i : Fin (spectralCount C)) :
    Matrix (Fin q) (Fin q) (field C f) :=
  fun j k => targetValue K₀ (constants C f) (.inr (.inr (.inl (i, j, k))))

/-- The literal functional-calculus target in the common overfield. -/
def N (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) : Matrix (Fin q) (Fin q) (field C f) :=
  fun i j => targetValue K₀ (constants C f) (.inr (.inr (.inr (i, j))))

@[simp] theorem a_real (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ)
    (i : Fin (spectralCount C)) :
    (a C f i : ℝ) = RealSpectralInterpolation.scalar (realMatrix C) i := rfl

@[simp] theorem b_real (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ)
    (i : Fin (spectralCount C)) :
    (b C f i : ℝ) = f (RealSpectralInterpolation.scalar (realMatrix C) i) := rfl

@[simp] theorem P_real (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ)
    (i : Fin (spectralCount C)) (j k : Fin q) :
    (P C f i j k : ℝ) = RealSpectralInterpolation.projector (realMatrix C) i j k := rfl

@[simp] theorem N_real (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) (i j : Fin q) :
    (N C f i j : ℝ) = cfc f (realMatrix C) i j := rfl

@[simp] theorem sourceMatrix_real (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) :
    (sourceMatrix C f).map (field C f).val = realMatrix C := rfl

@[simp] theorem P_map_real (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ)
    (i : Fin (spectralCount C)) :
    (P C f i).map (field C f).val = RealSpectralInterpolation.projector (realMatrix C) i := rfl

@[simp] theorem N_map_real (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) :
    (N C f).map (field C f).val = cfc f (realMatrix C) := rfl

theorem a_injective (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) :
    Function.Injective (a C f) := by
  intro i j h
  exact RealSpectralInterpolation.scalar_injective (realMatrix C)
    (congrArg (fun x : field C f => (x : ℝ)) h)

variable [FiniteDimensional ℚ K₀]

/-- Finite source-field membership supplies algebraicity of every real source entry. -/
theorem realMatrix_isAlgebraic (C : Matrix (Fin q) (Fin q) K₀) (i j : Fin q) :
    IsAlgebraic ℚ (realMatrix C i j) :=
  (Algebra.IsAlgebraic.isAlgebraic (C i j)).algHom K₀.val

/-- Every constant adjoined to the fixed source field is algebraic. -/
theorem constants_isAlgebraic (C : Matrix (Fin q) (Fin q) K₀)
    (hC : (realMatrix C).IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ (realMatrix C), IsAlgebraic ℚ (f x)) :
    ∀ i, IsAlgebraic ℚ (constants C f i) := by
  intro i
  rcases i with i | i
  · exact AlgebraicSpectralData.isAlgebraic_of_mem_spectrum _ (realMatrix_isAlgebraic C)
      (RealSpectralInterpolation.scalar_mem _ i)
  · rcases i with i | i
    · exact hf _ (RealSpectralInterpolation.scalar_mem _ i)
    · rcases i with p | p
      · exact AlgebraicSpectralData.isAlgebraic_spectralProjector_entry _ hC
          (realMatrix_isAlgebraic C) _ p.2.1 p.2.2
      · exact AlgebraicSpectralData.isAlgebraic_cfc_entry _ hC
          (realMatrix_isAlgebraic C) f hf p.1 p.2

/-- The entire fixed spectral construction lives in one finite rational extension. -/
theorem finiteDimensional (C : Matrix (Fin q) (Fin q) K₀)
    (hC : (realMatrix C).IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ (realMatrix C), IsAlgebraic ℚ (f x)) :
    FiniteDimensional ℚ (field C f) :=
  extension_finiteDimensional K₀ (constants C f) (constants_isAlgebraic C hC f hf)

/-- A fixed basis of the target overfield; the source oracle may retain any supplied basis. -/
def basis (C : Matrix (Fin q) (Fin q) K₀) (hC : (realMatrix C).IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ (realMatrix C), IsAlgebraic ℚ (f x)) :
    Module.Basis (Fin (Module.finrank ℚ (field C f))) ℚ (field C f) :=
  extensionBasis K₀ (constants C f) (constants_isAlgebraic C hC f hf)

omit [FiniteDimensional ℚ K₀] in
/-- The actual source powers satisfy the exact spectral identity in the overfield. -/
theorem sourceMatrix_pow (C : Matrix (Fin q) (Fin q) K₀)
    (hC : (realMatrix C).IsHermitian) (f : ℝ → ℝ) (h : ℕ) :
    sourceMatrix C f ^ h = ∑ i, a C f i ^ h • P C f i := by
  apply Matrix.map_injective (field C f).val.injective
  have hp := map_pow ((field C f).val.toRingHom.mapMatrix) (sourceMatrix C f) h
  change (sourceMatrix C f ^ h).map (field C f).val =
    (∑ i, a C f i ^ h • P C f i).map (field C f).val
  rw [show (sourceMatrix C f ^ h).map (field C f).val = realMatrix C ^ h from hp]
  rw [RealSpectralInterpolation.matrix_pow_eq _ hC]
  ext j k
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, map_pow]
  rfl

omit [FiniteDimensional ℚ K₀] in
/-- The lifted target is exactly the sum using the lifted scalar target values. -/
theorem N_eq_sum (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ) :
    N C f = ∑ i, b C f i • P C f i := by
  apply Matrix.map_injective (field C f).val.injective
  change (N C f).map (field C f).val = (∑ i, b C f i • P C f i).map (field C f).val
  rw [N_map_real, RealSpectralInterpolation.cfc_eq_sum_projectors]
  ext j k
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul]
  rfl

omit [FiniteDimensional ℚ K₀] in
/-- Zero preservation descends through the injective literal real embedding. -/
theorem zero_lift (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ)
    (hzero : ∀ i, RealSpectralInterpolation.scalar (realMatrix C) i = 0 →
      f (RealSpectralInterpolation.scalar (realMatrix C) i) = 0) :
    ∀ i, a C f i = 0 → b C f i = 0 := by
  intro i hi
  apply Subtype.ext
  exact hzero i (congrArg (fun x : field C f => (x : ℝ)) hi)

omit [FiniteDimensional ℚ K₀] in
/-- Equal-length product compatibility descends through the same embedding. -/
theorem compatible_lift (C : Matrix (Fin q) (Fin q) K₀) (f : ℝ → ℝ)
    (hcompat : Compatible (RealSpectralInterpolation.scalar (realMatrix C))
      (fun i => f (RealSpectralInterpolation.scalar (realMatrix C) i))) :
    Compatible (a C f) (b C f) :=
  compatible_of_field_embedding (field C f).val.toRingHom _ _ hcompat

end PlanarHom.SpectralFieldPresentation
