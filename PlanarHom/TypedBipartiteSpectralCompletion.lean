import PlanarHom.TypedBipartiteSpectralTransport

/-! Typed same-side CFC requires positive definiteness only on X. A source
matrix may have any unused entries; its companions, including cross-B labels,
are retained literally. No spectral property of a completion is assumed. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
open SpectralFieldPresentation SpectralAvailability ProductCompatibility
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {Y : Type} [Fintype Y] [DecidableEq Y]
variable {q bt ut dt dimension : ℕ}

/-- Full raw-word typed CFC operation with arbitrary unused completion entries.
The only selected entries ever queried are the intrinsic X×X entries. -/
def typedCfcAppendReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q ⊕ Y) (Fin q ⊕ Y) K₀)
    (U : Fin ut → (Fin q ⊕ Y) → K₀)
    (D : Fin dt → Set (Fin q ⊕ Y)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range Sum.inl)
    (hpath : ∀ x y,B old x y → PathDomainTyping B old privateX x y)
    (htype : ∀ x y,B old x y → D x⊆Set.range Sum.inl ∧ D y⊆Set.range Sum.inl)
    (A : Matrix (Fin q) (Fin q) K₀) (hblock : ∀ i j,M old (.inl i) (.inl j)=A i j)
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
  let MN := supportedContext M old A
  let φ := inclusion A f
  let bF := basis A hC f hf
  let r := cfcAppendReduction b₀ MN U D B T old privateX hX hpath A
    (supportedContext_self M old A) hC f hf hzero hcompat
  have hc := supportedContext_congr M old A hblock D B htype
  apply r.transport
    (domainEvaluationProblem bF
      (appendOne (fun l i j=>φ (M l i j)) (zeroExtend (N A f)))
      (fun l i=>φ (U l i)) (fun _=>1) D (appendOne B (B old)) T)
    (domainEvaluationProblem b₀ M U (fun _=>1) D B T)
    (fun _ h=>h) (fun _ h=>h) ?_ ?_
  · intro raw hr
    apply domain_value_congr bF _ _ _ _ D (appendOne B (B old)) T ?_ raw hr
    intro l
    refine Fin.addCases (fun l=>?_) (fun l=>?_) l
    · intro x y hl i hi j hj
      simp only [appendOne_old] at hl ⊢
      exact congrArg φ (hc l x y hl i hi j hj).symm
    · intro x y hl i hi j hj
      have hl0 : l=(0:Fin 1) := Subsingleton.elim _ _
      subst l
      have he : Fin.natAdd bt (0:Fin 1)=Fin.last bt := Fin.ext (Nat.add_zero bt)
      simp only [he,appendOne_aux]
  · intro raw hr
    exact domain_value_congr b₀ M MN U (fun _=>1) D B T
      (fun l x y hl i hi j hj=>(hc l x y hl i hi j hj).symm) raw hr

/-- Genuine rational powers on X in the joint original mixed context. In
particular r=0 is the identity on X, never a full ambient identity. -/
def typedRationalPowerAppendReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q ⊕ Y) (Fin q ⊕ Y) K₀)
    (U : Fin ut → (Fin q ⊕ Y) → K₀)
    (D : Fin dt → Set (Fin q ⊕ Y)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range Sum.inl)
    (hpath : ∀ x y,B old x y → PathDomainTyping B old privateX x y)
    (htype : ∀ x y,B old x y → D x⊆Set.range Sum.inl ∧ D y⊆Set.range Sum.inl)
    (A : Matrix (Fin q) (Fin q) K₀) (hblock : ∀ i j,M old (.inl i) (.inl j)=A i j)
    (hpd : (realMatrix A).PosDef) (r : ℚ) :=
  typedCfcAppendReduction b₀ M U D B T old privateX hX hpath htype A hblock hpd.1
    (fun x=>x^(r:ℝ)) (powerFunction_algebraic A hpd r) (powerFunction_zero A hpd r)
    (PositiveUnaryRationalPowers.compatible_real_rpow _ (RealSpectralInterpolation.scalar_pos _ hpd) r)

def typedRationalPowerAppend_joint (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q ⊕ Y) (Fin q ⊕ Y) K₀)
    (U : Fin ut → (Fin q ⊕ Y) → K₀)
    (D : Fin dt → Set (Fin q ⊕ Y)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range Sum.inl)
    (hpath : ∀ x y,B old x y → PathDomainTyping B old privateX x y)
    (htype : ∀ x y,B old x y → D x⊆Set.range Sum.inl ∧ D y⊆Set.range Sum.inl)
    (A : Matrix (Fin q) (Fin q) K₀) (hblock : ∀ i j,M old (.inl i) (.inl j)=A i j)
    (hpd : (realMatrix A).PosDef) (r : ℚ) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (domainEvaluationProblem b₀ M U (fun _=>1) D B T) base) :=
  (typedRationalPowerAppendReduction b₀ M U D B T old privateX hX hpath htype A hblock hpd r).trans available

end PlanarHom.TypedBipartiteSpectral
