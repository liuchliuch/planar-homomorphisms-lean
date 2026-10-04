import PlanarHom.RelativeRealSpectralData
import PlanarHom.WeightedSpectralField

/-! NEW finite spectral extension of an arbitrary represented real source field.
Every adjoined constant is proved algebraic over that field, rather than over Q.
The scalar and projector values are the actual real weighted-chain spectrum. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RelativeWeightedSpectralField
open PositiveWeightRemoval
variable {F:Type} [Field F] [Algebra F ℝ] {q:ℕ}

def realMatrix (A:Matrix (Fin q) (Fin q) F) := A.map (algebraMap F ℝ)
def realWeights (w:Fin q→F) := fun i=>algebraMap F ℝ (w i)
def spectralMatrix (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F) :=
  weightedConjugate (realMatrix A) (realWeights w)
abbrev Index (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F) :=
  Fin (Nat.card (spectrum ℝ (spectralMatrix A w))) ⊕
    (Fin (Nat.card (spectrum ℝ (spectralMatrix A w)))×Fin q×Fin q)
def constants (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F) : Index A w→ℝ :=
  Sum.elim (RealSpectralInterpolation.scalar (spectralMatrix A w))
    (fun p=>scaledProjector (realMatrix A) (realWeights w) p.1 p.2.1 p.2.2)

private theorem sqrt_algebraic (w:Fin q→F) (hw:∀i,0<realWeights w i) (i:Fin q) :
    IsAlgebraic F (Real.sqrt (realWeights w i)) := by
  apply IsAlgebraic.of_pow (n:=2) (by norm_num)
  simpa only [Real.sq_sqrt (hw i).le] using isAlgebraic_algebraMap (R:=F) (A:=ℝ) (w i)

theorem sqrtDiagonal_algebraic (w:Fin q→F) (hw:∀i,0<realWeights w i) (i j:Fin q) :
    IsAlgebraic F (sqrtDiagonal (realWeights w) i j) := by
  by_cases h:i=j
  · subst j
    simpa only [sqrtDiagonal,Matrix.diagonal_apply_eq] using sqrt_algebraic w hw i
  · simp only [sqrtDiagonal,Matrix.diagonal_apply_ne _ h]
    exact isAlgebraic_zero

theorem invSqrtDiagonal_algebraic (w:Fin q→F) (hw:∀i,0<realWeights w i) (i j:Fin q) :
    IsAlgebraic F (invSqrtDiagonal (realWeights w) i j) := by
  by_cases h:i=j
  · subst j
    simpa only [invSqrtDiagonal,Matrix.diagonal_apply_eq] using (sqrt_algebraic w hw i).inv
  · simp only [invSqrtDiagonal,Matrix.diagonal_apply_ne _ h]
    exact isAlgebraic_zero

theorem spectralMatrix_algebraic (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F)
    (hw:∀i,0<realWeights w i) : ∀i j,IsAlgebraic F (spectralMatrix A w i j) :=
  RelativeRealSpectralData.isAlgebraic_mul_entry _ _
    (RelativeRealSpectralData.isAlgebraic_mul_entry _ _ (sqrtDiagonal_algebraic w hw)
      (fun i j=>isAlgebraic_algebraMap (A i j))) (sqrtDiagonal_algebraic w hw)

theorem constants_algebraic (A:Matrix (Fin q) (Fin q) F) (hA:(realMatrix A).PosDef)
    (w:Fin q→F) (hw:∀i,0<realWeights w i) : ∀i,IsAlgebraic F (constants A w i) := by
  intro i
  rcases i with i|i
  · exact RelativeRealSpectralData.isAlgebraic_of_mem_spectrum _ (spectralMatrix_algebraic A w hw)
      (RealSpectralInterpolation.scalar_mem _ i)
  · exact RelativeRealSpectralData.isAlgebraic_mul_entry _ _
      (RelativeRealSpectralData.isAlgebraic_mul_entry _ _ (invSqrtDiagonal_algebraic w hw)
        (RelativeRealSpectralData.isAlgebraic_spectralProjector_entry _
          (weightedConjugate_posDef (realMatrix A) hA (realWeights w) hw).1
          (spectralMatrix_algebraic A w hw) _))
      (invSqrtDiagonal_algebraic w hw) i.2.1 i.2.2

def field (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F) : IntermediateField F ℝ :=
  IntermediateField.adjoin F (Set.range (constants A w))

theorem finiteDimensional (A:Matrix (Fin q) (Fin q) F) (hA:(realMatrix A).PosDef)
    (w:Fin q→F) (hw:∀i,0<realWeights w i) : FiniteDimensional F (field A w) := by
  apply IntermediateField.finiteDimensional_adjoin
  rintro _ ⟨i,rfl⟩
  exact (constants_algebraic A hA w hw i).isIntegral

def liftedConstant (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F) (i:Index A w) : field A w :=
  ⟨constants A w i,IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
def scalar (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F)
    (i:Fin (Nat.card (spectrum ℝ (spectralMatrix A w)))) : field A w := liftedConstant A w (.inl i)
def projector (A:Matrix (Fin q) (Fin q) F) (w:Fin q→F)
    (i:Fin (Nat.card (spectrum ℝ (spectralMatrix A w)))) : Matrix (Fin q) (Fin q) (field A w) :=
  fun j k=>liftedConstant A w (.inr (i,j,k))

theorem chain (A:Matrix (Fin q) (Fin q) F) (hA:(realMatrix A).PosDef)
    (w:Fin q→F) (hw:∀i,0<realWeights w i) (n:ℕ) (hn:0<n) :
    Complexity.MixedCode.weightedChain (A.map (algebraMap F (field A w)))
      (fun i=>algebraMap F (field A w) (w i)) n = ∑i,scalar A w i^n • projector A w i := by
  apply Matrix.map_injective (field A w).val.injective
  dsimp only
  rw [map_weightedChain (field A w).val.toRingHom]
  change Complexity.MixedCode.weightedChain (realMatrix A) (realWeights w) n = _
  rw [weightedChain_spectral (realMatrix A) hA (realWeights w) hw n hn]
  ext i j
  simp only [Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,map_sum,map_mul,map_pow]
  rfl

theorem projector_sum (A:Matrix (Fin q) (Fin q) F) (hA:(realMatrix A).PosDef)
    (w:Fin q→F) (hw:∀i,0<realWeights w i) :
    (∑i,projector A w i)=(Matrix.diagonal (fun i=>(w i)⁻¹)).map (algebraMap F (field A w)) := by
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  change (field A w).val.toRingHom ((∑k,projector A w k) i j)=_
  simp only [Matrix.sum_apply,map_sum]
  change (∑k,scaledProjector (realMatrix A) (realWeights w) k i j)=_
  have h:=congrFun (congrFun (scaledProjector_sum (realMatrix A) hA (realWeights w) hw) i) j
  by_cases hij:i=j
  · subst j
    simpa [Matrix.sum_apply,realWeights,Matrix.map_apply] using h
  · simpa [Matrix.sum_apply,realWeights,Matrix.map_apply,Matrix.diagonal_apply_ne _ hij] using h

end PlanarHom.RelativeWeightedSpectralField
