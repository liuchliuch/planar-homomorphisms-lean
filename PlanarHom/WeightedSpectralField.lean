import PlanarHom.WeightedDiagonalCongruence
import PlanarHom.SpectralFieldPresentation

/-! One fixed extension of the original source field contains the actual
weighted-chain spectral scalars and exterior-scaled projectors. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PositiveWeightRemoval
open AlgebraicProductInterpolation SpectralFieldPresentation
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀] {q : ℕ}

private theorem sqrt_algebraic {x : ℝ} (hx : 0≤x) (ha : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ (Real.sqrt x) := by
  apply IsAlgebraic.of_pow (n:=2) (by norm_num)
  simpa only [Real.sq_sqrt hx] using ha

def realWeights (w : Fin q → K₀) : Fin q → ℝ := fun i => w i

def weightedSpectralMatrix (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀) : Matrix (Fin q) (Fin q) ℝ :=
  weightedConjugate (realMatrix A) (realWeights w)

def WeightedConstantIndex (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀) :=
  Fin (Nat.card (spectrum ℝ (weightedSpectralMatrix A w))) ⊕
    (Fin (Nat.card (spectrum ℝ (weightedSpectralMatrix A w))) × Fin q × Fin q)

instance (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀) : Fintype (WeightedConstantIndex A w) :=
  inferInstanceAs (Fintype (_ ⊕ _))

def weightedConstants (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀) : WeightedConstantIndex A w → ℝ :=
  Sum.elim (RealSpectralInterpolation.scalar (weightedSpectralMatrix A w))
    (fun p => scaledProjector (realMatrix A) (realWeights w) p.1 p.2.1 p.2.2)

theorem sqrtDiagonal_algebraic (w : Fin q → K₀) (hw : ∀ i,0<(w i : ℝ)) (i j : Fin q) :
    IsAlgebraic ℚ (sqrtDiagonal (realWeights w) i j) := by
  by_cases h : i=j
  · subst j
    simpa only [sqrtDiagonal,Matrix.diagonal_apply_eq,realWeights] using
      sqrt_algebraic (hw i).le ((Algebra.IsAlgebraic.isAlgebraic (w i)).algHom K₀.val)
  · simp only [sqrtDiagonal,Matrix.diagonal_apply_ne _ h]
    exact isAlgebraic_zero

theorem invSqrtDiagonal_algebraic (w : Fin q → K₀) (hw : ∀ i,0<(w i : ℝ)) (i j : Fin q) :
    IsAlgebraic ℚ (invSqrtDiagonal (realWeights w) i j) := by
  by_cases h : i=j
  · subst j
    simpa only [invSqrtDiagonal,Matrix.diagonal_apply_eq,realWeights] using
      (sqrt_algebraic (hw i).le ((Algebra.IsAlgebraic.isAlgebraic (w i)).algHom K₀.val)).inv
  · simp only [invSqrtDiagonal,Matrix.diagonal_apply_ne _ h]
    exact isAlgebraic_zero

theorem weightedSpectralMatrix_algebraic (A : Matrix (Fin q) (Fin q) K₀)
    (w : Fin q → K₀) (hw : ∀ i,0<(w i : ℝ)) :
    ∀ i j,IsAlgebraic ℚ (weightedSpectralMatrix A w i j) :=
  AlgebraicSpectralData.isAlgebraic_mul_entry _ _
    (AlgebraicSpectralData.isAlgebraic_mul_entry _ _ (sqrtDiagonal_algebraic w hw) (realMatrix_isAlgebraic A))
    (sqrtDiagonal_algebraic w hw)

theorem weightedConstants_algebraic (A : Matrix (Fin q) (Fin q) K₀) (hA : (realMatrix A).PosDef)
    (w : Fin q → K₀) (hw : ∀ i,0<(w i : ℝ)) :
    ∀ i,IsAlgebraic ℚ (weightedConstants A w i) := by
  intro i
  rcases i with i|i
  · exact AlgebraicSpectralData.isAlgebraic_of_mem_spectrum _ (weightedSpectralMatrix_algebraic A w hw)
      (RealSpectralInterpolation.scalar_mem _ i)
  · exact AlgebraicSpectralData.isAlgebraic_mul_entry _ _
      (AlgebraicSpectralData.isAlgebraic_mul_entry _ _ (invSqrtDiagonal_algebraic w hw)
        (AlgebraicSpectralData.isAlgebraic_spectralProjector_entry _
          (weightedConjugate_posDef (realMatrix A) hA (realWeights w) hw).1
          (weightedSpectralMatrix_algebraic A w hw) _))
      (invSqrtDiagonal_algebraic w hw) i.2.1 i.2.2

def weightedField (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀) : IntermediateField ℚ ℝ :=
  extensionField K₀ (weightedConstants A w)

def weightedInclusion (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀) : K₀ →ₐ[ℚ] weightedField A w :=
  sourceInclusion K₀ (weightedConstants A w)

def weightedBasis (A : Matrix (Fin q) (Fin q) K₀) (hA : (realMatrix A).PosDef)
    (w : Fin q → K₀) (hw : ∀ i,0<(w i : ℝ)) :
    Module.Basis (Fin (Module.finrank ℚ (weightedField A w))) ℚ (weightedField A w) :=
  extensionBasis K₀ (weightedConstants A w) (weightedConstants_algebraic A hA w hw)

def weightedScalar (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀)
    (i : Fin (Nat.card (spectrum ℝ (weightedSpectralMatrix A w)))) : weightedField A w :=
  targetValue K₀ (weightedConstants A w) (.inl i)

def weightedProjector (A : Matrix (Fin q) (Fin q) K₀) (w : Fin q → K₀)
    (i : Fin (Nat.card (spectrum ℝ (weightedSpectralMatrix A w)))) :
    Matrix (Fin q) (Fin q) (weightedField A w) :=
  fun j k => targetValue K₀ (weightedConstants A w) (.inr (i,j,k))

/-- Mapping a weighted chain preserves all matrix products and diagonal factors. -/
theorem map_weightedChain {K L : Type} [Field K] [Field L]
    (φ : K →+* L) (A : Matrix (Fin q) (Fin q) K) (w : Fin q → K) (n : ℕ) :
    (Complexity.MixedCode.weightedChain A w n).map φ =
      Complexity.MixedCode.weightedChain (A.map φ) (fun i=>φ (w i)) n := by
  unfold Complexity.MixedCode.weightedChain
  change φ.mapMatrix (A * (Matrix.diagonal w * A)^(n-1)) = _
  rw [map_mul,map_pow,map_mul]
  have hd : φ.mapMatrix (Matrix.diagonal w)=Matrix.diagonal (fun i=>φ (w i)) := by
    ext i j
    by_cases h : i=j <;> simp [Matrix.diagonal_apply,h]
  rw [hd]
  rfl

theorem weighted_field_chain (A : Matrix (Fin q) (Fin q) K₀) (hA : (realMatrix A).PosDef)
    (w : Fin q → K₀) (hw : ∀ i,0<(w i : ℝ)) (n : ℕ) (hn : 0<n) :
    Complexity.MixedCode.weightedChain (A.map (weightedInclusion A w))
      (fun i=>weightedInclusion A w (w i)) n =
      ∑ i,weightedScalar A w i^n • weightedProjector A w i := by
  apply Matrix.map_injective (weightedField A w).val.injective
  dsimp only
  rw [map_weightedChain (weightedField A w).val.toRingHom]
  change Complexity.MixedCode.weightedChain (realMatrix A) (realWeights w) n = _
  rw [weightedChain_spectral (realMatrix A) hA (realWeights w) hw n hn]
  ext i j
  simp only [Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,map_sum,map_mul,map_pow]
  rfl

theorem weighted_field_projector_sum (A : Matrix (Fin q) (Fin q) K₀) (hA : (realMatrix A).PosDef)
    (w : Fin q → K₀) (hw : ∀ i,0<(w i : ℝ)) :
    (∑ i,weightedProjector A w i) =
      (Matrix.diagonal (fun i=>(w i)⁻¹)).map (weightedInclusion A w) := by
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  change (weightedField A w).val.toRingHom ((∑ k, weightedProjector A w k) i j) = _
  simp only [Matrix.sum_apply,map_sum]
  change (∑ k,scaledProjector (realMatrix A) (realWeights w) k i j) = _
  have h := congrFun (congrFun (scaledProjector_sum (realMatrix A) hA (realWeights w) hw) i) j
  by_cases hij : i=j
  · subst j
    simpa [Matrix.sum_apply,realWeights,Matrix.map_apply,weightedInclusion,sourceInclusion] using h
  · simpa [Matrix.sum_apply,realWeights,Matrix.map_apply,Matrix.diagonal_apply_ne _ hij,weightedInclusion,sourceInclusion] using h

end PlanarHom.PositiveWeightRemoval
