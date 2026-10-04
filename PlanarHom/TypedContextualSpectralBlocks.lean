import PlanarHom.TypedBipartiteContext
import PlanarHom.SpectralRealAvailability

/-! Literal X blocks, their algebraicity, and the two coordinate charts used
by the retained-context spectral programs. No spectral completion is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases
open TypedBipartiteSpectral SpectralFieldPresentation
variable {x y bt ut : ℕ}

@[simp] theorem domains_zero : domains x y 0=Set.range (leftEmbedding (q:=x) (y:=y)) := rfl

/-- Literal X-only source field block, with no information taken from Y. -/
def sourceBlock (L : RealLanguage (x+y) bt ut) (old : Fin bt) :
    Matrix (Fin x) (Fin x) L.field :=
  fun i j=>L.matricesK old (leftEmbedding i) (leftEmbedding j)

theorem sourceBlock_real (L : RealLanguage (x+y) bt ut) (old : Fin bt)
    (H : Matrix (Fin x) (Fin x) ℝ) (hH : L.matrices old=zeroExtendFin H) :
    realMatrix (sourceBlock L old)=H := by
  ext i j
  change L.matrices old (leftEmbedding i) (leftEmbedding j)=H i j
  rw [hH,zeroExtendFin_left]

theorem zeroExtendFin_algebraic (H : Matrix (Fin x) (Fin x) ℝ)
    (hH : ∀i j,IsAlgebraic ℚ (H i j)) :
    ∀i j,IsAlgebraic ℚ (zeroExtendFin (y:=y) H i j) := by
  intro i j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i|i <;> rcases j with j|j <;>
    simp only [zeroExtendFin,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,zeroExtend_inl,zeroExtend_inr_left,zeroExtend_inr_right]
  · exact hH i j
  all_goals exact isAlgebraic_zero

theorem algebraic_of_zeroExtendFin (H : Matrix (Fin x) (Fin x) ℝ)
    (hH : ∀i j,IsAlgebraic ℚ (zeroExtendFin (y:=y) H i j)) :
    ∀i j,IsAlgebraic ℚ (H i j) := by
  intro i j
  simpa only [zeroExtendFin_left] using hH (leftEmbedding i) (leftEmbedding j)

theorem sameX_path (B : Fin bt→Fin 2→Fin 2→Prop) (old : Fin bt)
    (hB : B old=sameX) : ∀a b,B old a b→PathDomainTyping B old 0 a b := by
  intro a b hab
  rw [hB] at hab
  obtain ⟨rfl,rfl⟩ := hab
  simp [PathDomainTyping,hB,sameX]

theorem sameX_type (B : Fin bt→Fin 2→Fin 2→Prop) (old : Fin bt)
    (hB : B old=sameX) : ∀a b,B old a b→
      domains x y a⊆Set.range (leftEmbedding (q:=x) (y:=y)) ∧
      domains x y b⊆Set.range (leftEmbedding (q:=x) (y:=y)) := by
  intro a b hab
  rw [hB] at hab
  obtain ⟨rfl,rfl⟩ := hab
  exact ⟨Set.Subset.rfl,Set.Subset.rfl⟩

/-- The rational program's intrinsic domain is the strict pullback of the
finite numeric domain, not an independently chosen domain chart. -/
theorem sumDomains_zero :
    (finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y)) ⁻¹' domains x y 0=Set.range Sum.inl := by
  ext c
  rcases c with i|i
  · simp [domains]
  · simp only [domains,Fin.cases_zero,Set.mem_preimage,Set.mem_range,finSumFinEquiv_apply_right,Sum.inl_ne_inr,exists_false,iff_false]
    rintro ⟨j,hj⟩
    have := congrArg Fin.val hj
    change j.val=x+i.val at this
    omega

theorem sum_sameX_type (B : Fin bt→Fin 2→Fin 2→Prop) (old : Fin bt)
    (hB : B old=sameX) : ∀a b,B old a b→
      (finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y)) ⁻¹' domains x y a⊆Set.range Sum.inl ∧
      (finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y)) ⁻¹' domains x y b⊆Set.range Sum.inl := by
  intro a b hab
  rw [hB] at hab
  obtain ⟨rfl,rfl⟩ := hab
  rw [sumDomains_zero]
  exact ⟨Set.Subset.rfl,Set.Subset.rfl⟩

/-- Exact zero-extension commutes with literal real-field embeddings. -/
theorem zeroExtendFin_coe {K : IntermediateField ℚ ℝ}
    (H : Matrix (Fin x) (Fin x) K) (i j : Fin (x+y)) :
    (zeroExtendFin H i j:ℝ)=zeroExtendFin (fun a b=>(H a b:ℝ)) i j := by
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [zeroExtendFin,Matrix.reindex_apply,zeroExtend,Matrix.fromBlocks]

/-- The pullback is literally the same supported X matrix. -/
theorem zeroExtendFin_pullback {K : Type} [Field K] (H : Matrix (Fin x) (Fin x) K) :
    (fun i j=>zeroExtendFin (y:=y) H (finSumFinEquiv i) (finSumFinEquiv j))=zeroExtend H := by
  ext i j
  simp [zeroExtendFin,Matrix.reindex_apply]

/-- Old labels and the appended X matrix share one and the same color chart. -/
theorem appendZero_pullback {K : Type} [Field K]
    (M : Fin bt→Matrix (Fin (x+y)) (Fin (x+y)) K)
    (H : Matrix (Fin x) (Fin x) K) :
    (fun l i j=>appendOne M (zeroExtendFin H) l (finSumFinEquiv i) (finSumFinEquiv j))=
      appendOne (fun l i j=>M l (finSumFinEquiv i) (finSumFinEquiv j)) (zeroExtend H) := by
  funext l
  refine Fin.addCases (fun a=>?_) (fun a=>?_) l
  · simp only [appendOne_old]
  · simpa only [appendOne,Fin.addCases_right] using zeroExtendFin_pullback H

end PlanarHom.TypedBipartiteContext
