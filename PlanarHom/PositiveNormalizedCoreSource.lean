import PlanarHom.PositiveNormalizationSourcePrograms
import PlanarHom.PositiveUnitDiagonalSourceRigidity
import PlanarHom.FiniteFieldQuotientLanguage

/-! NEW original positive-source normalized-core classification. The actual
loop/power/endpoint program constructs the normalization, actual twin quotienting
retains summed source weights, and source rigidity proves the core tensor form.
Only the independent all-q Potts premise remains explicit. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode Boolean
variable {q bt ut : ℕ} [Nonempty (Fin q)]

theorem normalized_quotient_tensor_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hp : ∀i j,0<L.matrices old i j) (hw : ∀i,0<L.weights i)
    (hnot : ¬PromisedSharpPHard L.problem) :
    ∃ d : ℕ, ∃ eQ : Quotient (Twins.rowSetoid (diagonalNormalize (L.matrices old))) ≃ Cube d,
    ∃ ρ : Fin d → ℝ, (∀r,0<ρ r ∧ ρ r≠1) ∧
      ∀r s,Twins.quotientMatrix (diagonalNormalize (L.matrices old))
        (diagonalNormalize_symmetric _ hs) r s = tensor ρ (eQ r) (eQ s) := by
  obtain ⟨F,h₀,n,bF,C,hC,hr⟩ := PositiveNormalizationSourcePrograms.exists_normalized_moment_sources
    L.basis L.matricesK L.unariesK L.weightsK old (fun i=>hp i i)
  change ∀i j,(C i j:ℝ)=diagonalNormalize (L.matrices old) i j at hC
  have hsC : ∀i j,C i j=C j i := by
    intro i j
    apply Subtype.ext
    rw [hC,hC]
    exact diagonalNormalize_symmetric _ hs i j
  have hpC : ∀i j,0<(C i j:ℝ) := by
    intro i j
    rw [hC]
    exact diagonalNormalize_positive _ hp i j
  have hdC : ∀i,(C i i:ℝ)=1 := by
    intro i
    rw [hC]
    exact diagonalNormalize_diagonal _ (fun i=>hp i i) i
  let wF : Fin q → F := fun i=>IntermediateField.inclusion h₀ (L.weightsK i)
  obtain ⟨red⟩ := hr 0
  have rC : PromisePolyTimeTuringReduction
      (evaluationProblem bF (fun _:Fin 1=>C) (fun u:Fin 0=>u.elim0) wF) L.problem := by
    simpa only [pow_zero,mul_one] using red
  let S := FiniteFieldQuotientLanguage.language bF C hsC wF
  have rS := (FiniteFieldQuotientLanguage.reduction bF C hsC wF).trans
    ((ActualTwins.quotientReduction bF C hsC wF).trans rC)
  letI : Nonempty (Quotient (Twins.rowSetoid C)) := ⟨Quotient.mk _ (Classical.arbitrary (Fin q))⟩
  letI : Nonempty (Fin (Fintype.card (Quotient (Twins.rowSetoid C)))) := ⟨⟨0,Fintype.card_pos⟩⟩
  letI : IsStrictOrderedRing F := Subfield.toIsStrictOrderedRing F.toSubfield
  have hsS : ∀i j,S.matrices 0 i j=S.matrices 0 j i := fun i j=>
    congrArg (fun z:F=>(z:ℝ)) (FiniteFieldQuotientLanguage.matrix_symmetric C hsC i j)
  have hpS : ∀i j,0<S.matrices 0 i j := FiniteFieldQuotientLanguage.real_matrix_pos C hsC hpC
  have hdS : ∀i,S.matrices 0 i i=1 := FiniteFieldQuotientLanguage.real_matrix_diag C hsC hdC
  have hiS : Function.Injective (S.matrices 0) := FiniteFieldQuotientLanguage.real_matrix_rows_injective C hsC
  have hwS : ∀i,0<S.weights i := fun i=>Twins.quotientWeight_pos C wF hw _
  obtain ⟨d,e,ρ,hρ,he,hU⟩ := S.weighted_unit_diagonal_tensor_of_not_hard
    hPotts 0 hsS hpS hdS hiS hwS (fun hh=>hnot (hh.trans rS))
  let er := FiniteFieldQuotientLanguage.realQuotientEquiv C (diagonalNormalize (L.matrices old)) hC
  let ei := (FiniteFieldQuotientLanguage.index C).trans er
  refine ⟨d,ei.symm.trans e,ρ,hρ,?_⟩
  intro r s
  have hreal := FiniteFieldQuotientLanguage.quotientMatrix_real C hsC
    (diagonalNormalize (L.matrices old)) (diagonalNormalize_symmetric _ hs) hC
    (FiniteFieldQuotientLanguage.index C (ei.symm r)) (FiniteFieldQuotientLanguage.index C (ei.symm s))
  change S.matrices 0 (ei.symm r) (ei.symm s) =
    Twins.quotientMatrix (diagonalNormalize (L.matrices old)) (diagonalNormalize_symmetric _ hs)
      (ei (ei.symm r)) (ei (ei.symm s)) at hreal
  rw [ei.apply_symm_apply,ei.apply_symm_apply] at hreal
  have hentry := congrFun (congrFun he (e (ei.symm r))) (e (ei.symm s))
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply] at hentry
  exact hreal.symm.trans hentry

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
