import PlanarHom.TypedBipartiteSpectralEffectiveCompletion

/-! Source-facing effective spectral closure with literal algebraic real target
entries, one fixed finite overfield, and the original source answer basis. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
open EffectiveProductTransfer SpectralFieldPresentation AlgebraicProductInterpolation
variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q y bt ut dt dimension : ℕ}

/-- Actual typed effective3.10(S), retaining the original fixed source field.
Every analytic hypothesis concerns A on X. The chosen x₀ only repeats an
existing X entry at unused positions during the finite sampling computation. -/
def typedEffectiveOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin (q+y)) (Fin (q+y)) K₀)
    (U : Fin ut → Fin (q+y) → K₀)
    (D : Fin dt → Set (Fin (q+y))) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range (leftEmbedding (q:=q) (y:=y)))
    (hpath : ∀ x z,B old x z → PathDomainTyping B old privateX x z)
    (htype : ∀ x z,B old x z → D x⊆Set.range (leftEmbedding (q:=q) (y:=y)) ∧
      D z⊆Set.range (leftEmbedding (q:=q) (y:=y)))
    (A : Matrix (Fin q) (Fin q) K₀)
    (hblock : ∀ i j,M old (leftEmbedding i) (leftEmbedding j)=A i j)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j,IsAlgebraic ℚ (N i j))
    (x₀ : Fin q) (hpd : (realMatrix A).PosDef) (hNs : N.IsHermitian)
    (n₀ : ℕ) (hn₀ : 1≤n₀)
    (hp : ∀ n,n₀≤n → ∀ i j,0<matrixPowerRealFamily A n i j)
    (hi : ProductIdentities (matrixPowerRealFamily A) N) :
    let entries := fun p : Fin q×Fin q=>N p.1 p.2
    let φ := sourceInclusion K₀ entries
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (extensionBasis K₀ entries (fun p=>hN p.1 p.2))
        (appendOne (fun l i j=>φ (M l i j))
          (zeroExtendFin (fun i j=>targetValue K₀ entries (i,j))))
        (fun l i=>φ (U l i)) (fun _=>1) D (appendOne B (B old)) T)
      (domainEvaluationProblem b₀ M U (fun _=>1) D B T) := by
  dsimp only
  let entries := fun p : Fin q×Fin q=>N p.1 p.2
  let KF := extensionField K₀ entries
  letI : FiniteDimensional ℚ KF := extension_finiteDimensional K₀ entries (fun p=>hN p.1 p.2)
  let φ := sourceInclusion K₀ entries
  let bF := extensionBasis K₀ entries (fun p=>hN p.1 p.2)
  let MF := fun l i j=>φ (M l i j)
  let UF := fun l i=>φ (U l i)
  let AF : Matrix (Fin q) (Fin q) KF := fun i j=>φ (A i j)
  let NF : Matrix (Fin q) (Fin q) KF := fun i j=>targetValue K₀ entries (i,j)
  have hblockF : ∀ i j,MF old (leftEmbedding i) (leftEmbedding j)=AF i j := by
    intro i j
    exact congrArg φ (hblock i j)
  have hNsF : ∀ i j,NF i j=NF j i := by
    intro i j
    apply Subtype.ext
    exact hNs.apply j i
  have hpF : ∀ n,n₀≤n → ∀ i j,0<matrixPowerRealFamily AF n i j := hp
  have hiF : ProductIdentities (matrixPowerRealFamily AF) (fun i j=>(NF i j:ℝ)) := hi
  let first := typedEffectiveAppendReduction bF MF UF D B T old privateX hX hpath htype
    AF NF hblockF x₀ hpd hNsF n₀ hn₀ hpF hiF
  have second : PromisePolyTimeTuringReduction
      (domainEvaluationProblem bF MF UF (fun _=>1) D B T)
      (domainEvaluationProblem b₀ M U (fun _=>1) D B T) := by
    simpa only [map_one] using domainFieldMapReduction b₀ bF φ M U (fun _=>1) D B T
  exact first.trans second

/-- Compose the entire joint mixed context with the actual original oracle. -/
def typedEffectiveOverfield_joint (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin (q+y)) (Fin (q+y)) K₀)
    (U : Fin ut → Fin (q+y) → K₀)
    (D : Fin dt → Set (Fin (q+y))) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range (leftEmbedding (q:=q) (y:=y)))
    (hpath : ∀ x z,B old x z → PathDomainTyping B old privateX x z)
    (htype : ∀ x z,B old x z → D x⊆Set.range (leftEmbedding (q:=q) (y:=y)) ∧
      D z⊆Set.range (leftEmbedding (q:=q) (y:=y)))
    (A : Matrix (Fin q) (Fin q) K₀)
    (hblock : ∀ i j,M old (leftEmbedding i) (leftEmbedding j)=A i j)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j,IsAlgebraic ℚ (N i j))
    (x₀ : Fin q) (hpd : (realMatrix A).PosDef) (hNs : N.IsHermitian)
    (n₀ : ℕ) (hn₀ : 1≤n₀)
    (hp : ∀ n,n₀≤n → ∀ i j,0<matrixPowerRealFamily A n i j)
    (hi : ProductIdentities (matrixPowerRealFamily A) N)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (domainEvaluationProblem b₀ M U (fun _=>1) D B T) base) :=
  (typedEffectiveOverfieldReduction b₀ M U D B T old privateX hX hpath htype
    A hblock N hN x₀ hpd hNs n₀ hn₀ hp hi).trans available

end PlanarHom.TypedBipartiteSpectral
