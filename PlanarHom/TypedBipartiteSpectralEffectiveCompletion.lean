import PlanarHom.TypedBipartiteSpectralEffective

/-! Effective spectral closure ignores every entry outside the selected
intrinsic X×X type, while preserving arbitrary cross-side companion labels. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.TypedBipartiteSpectral
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
open EffectiveProductTransfer SpectralFieldPresentation
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q y bt ut dt dimension : ℕ}

/-- Same-side effective source3.10 with arbitrary unused selected completion.
The hypotheses are the paper's positivity and product identities on X only. -/
def typedEffectiveAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin (q+y)) (Fin (q+y)) K)
    (U : Fin ut → Fin (q+y) → K)
    (D : Fin dt → Set (Fin (q+y))) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range (leftEmbedding (q:=q) (y:=y)))
    (hpath : ∀ x z,B old x z → PathDomainTyping B old privateX x z)
    (htype : ∀ x z,B old x z → D x⊆Set.range (leftEmbedding (q:=q) (y:=y)) ∧
      D z⊆Set.range (leftEmbedding (q:=q) (y:=y)))
    (A N : Matrix (Fin q) (Fin q) K)
    (hblock : ∀ i j,M old (leftEmbedding i) (leftEmbedding j)=A i j)
    (x₀ : Fin q) (hpd : (realMatrix A).PosDef) (hNs : ∀ i j,N i j=N j i)
    (n₀ : ℕ) (hn₀ : 1≤n₀)
    (hp : ∀ n,n₀≤n → ∀ i j,0<matrixPowerRealFamily A n i j)
    (hi : ProductIdentities (matrixPowerRealFamily A) (fun i j=>(N i j:ℝ))) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (zeroExtendFin N)) U (fun _=>1)
        D (appendOne B (B old)) T)
      (domainEvaluationProblem basis M U (fun _=>1) D B T) := by
  let MN := fun l=>if l=old then zeroExtendFin A else M l
  have hMN : MN old=zeroExtendFin A := by simp [MN]
  have hc : ∀ l x z,B l x z → ∀ i∈D x,∀ j∈D z,MN l i j=M l i j := by
    intro l x z hl i hi j hj
    by_cases he : l=old
    · subst l
      obtain ⟨i,rfl⟩ := (htype x z hl).1 hi
      obtain ⟨j,rfl⟩ := (htype x z hl).2 hj
      simpa [MN] using (hblock i j).symm
    · simp [MN,he]
  let r := effectiveAppendReduction basis MN U D B T old privateX hX hpath htype
    A N hMN x₀ hpd hNs n₀ hn₀ hp hi
  apply r.transport
    (domainEvaluationProblem basis (appendOne M (zeroExtendFin N)) U (fun _=>1)
      D (appendOne B (B old)) T)
    (domainEvaluationProblem basis M U (fun _=>1) D B T)
    (fun _ h=>h) (fun _ h=>h) ?_ ?_
  · intro raw hr
    apply domain_value_congr basis _ _ U (fun _=>1) D (appendOne B (B old)) T ?_ raw hr
    intro l
    refine Fin.addCases (fun l=>?_) (fun l=>?_) l
    · intro x z hl i hi j hj
      simp only [appendOne_old] at hl ⊢
      exact (hc l x z hl i hi j hj).symm
    · intro x z hl i hi j hj
      have he : Fin.natAdd bt l=Fin.last bt := by
        have : l=(0:Fin 1) := Subsingleton.elim _ _
        subst l
        exact Fin.ext (Nat.add_zero bt)
      simp only [he,appendOne_aux]
  · intro raw hr
    exact domain_value_congr basis M MN U (fun _=>1) D B T
      (fun l x z hl i hi j hj=>(hc l x z hl i hi j hj).symm) raw hr

/-- Joint availability composes the entire typed mixed context, including all
cross companions, with its original base oracle. -/
def typedEffectiveAppend_joint (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin (q+y)) (Fin (q+y)) K)
    (U : Fin ut → Fin (q+y) → K)
    (D : Fin dt → Set (Fin (q+y))) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (old : Fin bt) (privateX : Fin dt)
    (hX : D privateX=Set.range (leftEmbedding (q:=q) (y:=y)))
    (hpath : ∀ x z,B old x z → PathDomainTyping B old privateX x z)
    (htype : ∀ x z,B old x z → D x⊆Set.range (leftEmbedding (q:=q) (y:=y)) ∧
      D z⊆Set.range (leftEmbedding (q:=q) (y:=y)))
    (A N : Matrix (Fin q) (Fin q) K)
    (hblock : ∀ i j,M old (leftEmbedding i) (leftEmbedding j)=A i j)
    (x₀ : Fin q) (hpd : (realMatrix A).PosDef) (hNs : ∀ i j,N i j=N j i)
    (n₀ : ℕ) (hn₀ : 1≤n₀)
    (hp : ∀ n,n₀≤n → ∀ i j,0<matrixPowerRealFamily A n i j)
    (hi : ProductIdentities (matrixPowerRealFamily A) (fun i j=>(N i j:ℝ)))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis M U (fun _=>1) D B T) base) :=
  (typedEffectiveAppendReduction basis M U D B T old privateX hX hpath htype
    A N hblock x₀ hpd hNs n₀ hn₀ hp hi).trans available

end PlanarHom.TypedBipartiteSpectral
