import PlanarHom.BipartiteTensorWeightAvailability
import PlanarHom.PositiveDefiniteDichotomyAssembly

/-! NEW conditional closure of the exact ordinary-source hard clause of 9.3.
The recovered left/right source programs are retained. Actual PD source
classification replaces the unavailable unconditional classification wrapper.
The prescribed-bipartition endpoint is outside this extracted module. -/
noncomputable section
open Classical
namespace PlanarHom.BipartiteTensorWeight
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity PositiveRealCore MatrixCoordinateTransport ClosedMatrixFamily
variable {q : ℕ}

theorem positive_nonconstant_diagonal_hard_of_potts (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hpd : (L.matrices 0).PosDef) (hpos : ∀i j,0<L.matrices 0 i j)
    (hnon : ∃i j,L.matrices 0 i i≠L.matrices 0 j j) : PromisedSharpPHard L.problem :=
  L.positive_nonconstant_diagonal_hard_of_potts hPotts hunit hpd hpos hnon

variable {I : Type} [Fintype I] [DecidableEq I]
variable (e : Fin q ≃ I ⊕ I) (L : RealLanguage q 1 0) (B : Matrix I I ℝ) (μ ν : I→ℝ)
variable (hM : ∀ i j,L.matrices 0 i j=doubleMatrix B (e i) (e j))
variable (hw : ∀ i,L.weights i=Sum.elim μ ν (e i))
variable (hμ : ∀ i,0<μ i) (hν : ∀ i,0<ν i)

include hM hw hμ hν in
theorem left_core_hard_of_potts (hPotts : PositivePottsFoundation) (hB : IsUnit B) (hpd : (leftGram B μ ν).PosDef)
    (hpos : ∀ i j,0<leftGram B μ ν i j)
    (hnon : ∃ i j,leftGram B μ ν i i≠leftGram B μ ν j j) : PromisedSharpPHard L.problem := by
  let S := leftLanguage e L μ ν hw hμ hν
  let f := leftCoordinate e
  have hm : S.matrices 0=Matrix.reindex f.symm f.symm (leftGram B μ ν) := by
    ext i j
    exact leftLanguage_matrix e L B μ ν hM hw hμ hν i j
  have hp : (S.matrices 0).PosDef := by rw [hm]; exact reindex_posDef f.symm hpd
  have hposS : ∀ i j,0<S.matrices 0 i j := by
    intro i j
    rw [hm]
    exact hpos (f i) (f j)
  have hnonS : ∃ i j,S.matrices 0 i i≠S.matrices 0 j j := by
    obtain ⟨i,j,hij⟩ := hnon
    refine ⟨f.symm i,f.symm j,?_⟩
    simpa only [hm,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,
      Equiv.apply_symm_apply] using hij
  exact (positive_nonconstant_diagonal_hard_of_potts hPotts S (fun _=>rfl) hp hposS hnonS).trans
    (leftSourceReduction e L B μ ν hM hw hμ hν hB)

include hM hw hμ hν in
theorem right_core_hard_of_potts (hPotts : PositivePottsFoundation) (hB : IsUnit B) (hpd : (rightGram B μ ν).PosDef)
    (hpos : ∀ i j,0<rightGram B μ ν i j)
    (hnon : ∃ i j,rightGram B μ ν i i≠rightGram B μ ν j j) : PromisedSharpPHard L.problem := by
  let S := rightLanguage e L μ ν hw hμ hν
  let f := rightCoordinate e
  have hm : S.matrices 0=Matrix.reindex f.symm f.symm (rightGram B μ ν) := by
    ext i j
    exact rightLanguage_matrix e L B μ ν hM hw hμ hν i j
  have hp : (S.matrices 0).PosDef := by rw [hm]; exact reindex_posDef f.symm hpd
  have hposS : ∀ i j,0<S.matrices 0 i j := by
    intro i j
    rw [hm]
    exact hpos (f i) (f j)
  have hnonS : ∃ i j,S.matrices 0 i i≠S.matrices 0 j j := by
    obtain ⟨i,j,hij⟩ := hnon
    refine ⟨f.symm i,f.symm j,?_⟩
    simpa only [hm,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,
      Equiv.apply_symm_apply] using hij
  exact (positive_nonconstant_diagonal_hard_of_potts hPotts S (fun _=>rfl) hp hposS hnonS).trans
    (rightSourceReduction e L B μ ν hM hw hμ hν hB)

variable {d : ℕ}

/-- Original Lemma 9.3: either nonconstant side weight forces actual source
hardness. Only the independent Potts foundation remains explicit; no source-availability hypothesis is supplied. -/
theorem nonconstant_weights_hard_of_potts
    (hPotts : PositivePottsFoundation)
    (e : Fin q ≃ Boolean.Cube d ⊕ Boolean.Cube d) (L : RealLanguage q 1 0)
    (c : ℝ) (hc : 0<c) (ρ : Fin d→ℝ) (hρ : ∀ r,0<ρ r) (hne : ∀ r,ρ r≠1)
    (μ ν : Boolean.Cube d→ℝ) (hμ : ∀ i,0<μ i) (hν : ∀ i,0<ν i)
    (hM : ∀ i j,L.matrices 0 i j=doubleMatrix (scaledTensor c ρ) (e i) (e j))
    (hw : ∀ i,L.weights i=Sum.elim μ ν (e i))
    (hnon : (∃ i j,μ i≠μ j) ∨ (∃ i j,ν i≠ν j)) : PromisedSharpPHard L.problem := by
  have hB : IsUnit (scaledTensor c ρ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (scaledTensor_det_ne_zero c hc ρ hρ hne))
  obtain ⟨hpdX,hpdY,hposX,hposY,hdiag⟩ := bipartite_ising_core c hc ρ hρ hne μ ν hμ hν hnon
  rcases hdiag with h | h
  · exact left_core_hard_of_potts e L _ μ ν hM hw hμ hν hPotts hB hpdX hposX h
  · exact right_core_hard_of_potts e L _ μ ν hM hw hμ hν hPotts hB hpdY hposY h

end PlanarHom.BipartiteTensorWeight
