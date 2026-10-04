import PlanarHom.TypedBipartiteSpectralReduction
import PlanarHom.TypedBipartiteSpectralBlocks
import PlanarHom.SpectralCFCOverfield
import PlanarHom.FieldPresentationReductions

/-! Actual typed spectral availability on X⊕Y, retaining arbitrary cross-side
companions, the prescribed endpoint tables, and the original answer basis.
The overfield is generated from the X block alone: no Y eigenvalue enters any
compatibility test or interpolation table. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode FiniteLanguageAliases PrescribedDomains
open SpectralFieldPresentation SpectralAvailability ProductCompatibility
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {Y : Type} [Fintype Y] [DecidableEq Y]
variable {q bt ut dt dimension : ℕ}

/-- A genuine CFC operation on the X block in a mixed ambient context. Only
private path vertices receive the already prescribed X domain. -/
def cfcAppendReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q ⊕ Y) (Fin q ⊕ Y) K₀)
    (U : Fin ut → (Fin q ⊕ Y) → K₀)
    (D : Fin dt → Set (Fin q ⊕ Y)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range Sum.inl)
    (hpath : ∀ x y,B old x y → PathDomainTyping B old privateX x y)
    (A : Matrix (Fin q) (Fin q) K₀) (hA : M old=zeroExtend A)
    (hC : (realMatrix A).IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x∈spectrum ℝ (realMatrix A),IsAlgebraic ℚ (f x))
    (hzero : ∀ i,RealSpectralInterpolation.scalar (realMatrix A) i=0 →
      f (RealSpectralInterpolation.scalar (realMatrix A) i)=0)
    (hcompat : Compatible (RealSpectralInterpolation.scalar (realMatrix A))
      (fun i => f (RealSpectralInterpolation.scalar (realMatrix A) i))) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (basis A hC f hf)
        (appendOne (fun l i j => inclusion A f (M l i j)) (zeroExtend (N A f)))
        (fun l i => inclusion A f (U l i)) (fun _=>1) D (appendOne B (B old)) T)
      (domainEvaluationProblem b₀ M U (fun _=>1) D B T) := by
  let φ := inclusion A f
  let bF := basis A hC f hf
  let MF : Fin bt → Matrix (Fin q ⊕ Y) (Fin q ⊕ Y) (field A f) := fun l i j=>φ (M l i j)
  let UF : Fin ut → (Fin q ⊕ Y) → field A f := fun l i=>φ (U l i)
  have hMF : MF old=zeroExtend (sourceMatrix A f) := by
    ext (i|i) (j|j) <;> simp [MF,φ,hA,zeroExtend,sourceMatrix,Matrix.map_apply]
  have hs : ∀ c,c∉D privateX → ∀ d,MF old c d=0 := by
    intro c hc d
    rw [hMF]
    rcases c with c|c
    · exact (hc (by rw [hX]; exact ⟨c,rfl⟩)).elim
    · exact zeroExtend_inr_left _ _ _
  have hp : ∀ n : ℕ,0<n → MF old^n=∑ i,a A f i^n • zeroExtend (P A f i) := by
    intro n hn
    rw [hMF,zeroExtend_pow _ n hn,sourceMatrix_pow A hC f n,zeroExtend_sum_smul]
  let first := supportedSpectralAppendReduction bF MF UF D B T old privateX hs hpath
    (fun i=>zeroExtend (P A f i)) (a A f) (b A f) hp
    (zero_lift A f hzero) (compatible_lift A f hcompat)
  have second : PromisePolyTimeTuringReduction
      (domainEvaluationProblem bF MF UF (fun _=>1) D B T)
      (domainEvaluationProblem b₀ M U (fun _=>1) D B T) := by
    simpa only [map_one] using domainFieldMapReduction b₀ bF φ M U (fun _=>1) D B T
  change PromisePolyTimeTuringReduction
    (domainEvaluationProblem bF (appendOne MF (zeroExtend (N A f))) UF (fun _=>1)
      D (appendOne B (B old)) T) _
  rw [N_eq_sum A f,zeroExtend_sum_smul]
  exact first.trans second

/-- All fixed rational exponents, including zero and negative exponents, of a
positive definite X block are available in the original typed mixed context. -/
def rationalPowerAppendReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q ⊕ Y) (Fin q ⊕ Y) K₀)
    (U : Fin ut → (Fin q ⊕ Y) → K₀)
    (D : Fin dt → Set (Fin q ⊕ Y)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range Sum.inl)
    (hpath : ∀ x y,B old x y → PathDomainTyping B old privateX x y)
    (A : Matrix (Fin q) (Fin q) K₀) (hA : M old=zeroExtend A)
    (hpd : (realMatrix A).PosDef) (r : ℚ) :=
  cfcAppendReduction b₀ M U D B T old privateX hX hpath A hA hpd.1
    (fun x=>x^(r:ℝ)) (powerFunction_algebraic A hpd r) (powerFunction_zero A hpd r)
    (PositiveUnaryRationalPowers.compatible_real_rpow _ (RealSpectralInterpolation.scalar_pos _ hpd) r)

/-- Composition retains the entire companion context and its source oracle. -/
def rationalPowerAppend_joint (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q ⊕ Y) (Fin q ⊕ Y) K₀)
    (U : Fin ut → (Fin q ⊕ Y) → K₀)
    (D : Fin dt → Set (Fin q ⊕ Y)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range Sum.inl)
    (hpath : ∀ x y,B old x y → PathDomainTyping B old privateX x y)
    (A : Matrix (Fin q) (Fin q) K₀) (hA : M old=zeroExtend A)
    (hpd : (realMatrix A).PosDef) (r : ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (domainEvaluationProblem b₀ M U (fun _=>1) D B T) base) :=
  (rationalPowerAppendReduction b₀ M U D B T old privateX hX hpath A hA hpd r).trans available

/-- The appended real block is literally the rational CFC power on X. -/
theorem rationalPower_target_real (A : Matrix (Fin q) (Fin q) K₀) (r : ℚ) (i j : Fin q) :
    ((zeroExtend (Y:=Y) (N A (fun x=>x^(r:ℝ)))) (.inl i) (.inl j) : ℝ)=
      RealSpectralInterpolation.rationalPower (realMatrix A) r i j := rfl

end PlanarHom.TypedBipartiteSpectral
