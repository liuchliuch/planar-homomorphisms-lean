/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.TractableRankOneBlockSourceConditional
import PlanarHom.PositiveAmplitudeReconstruction
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode IsingTensorTractability TractableBlockComposition
variable {q : ℕ}
def PositiveTensorForm (M : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  ∃ k d : ℕ,∃ e : Fin q≃Fin k×Boolean.Cube d,∃ a : Fin k→ℝ,∃ ρ : Fin d→ℝ,
    0<k ∧ (∀ i,0<a i) ∧ (∀ r,0<ρ r) ∧
      Matrix.reindex e e M=(fun i j=>a i.1*a j.1*Boolean.tensor ρ i.2 j.2)
theorem positiveTensorForm_inFP_of_ising (hIsing : BooleanTensorEasyAssembly.PositiveIsingFoundation) (L : RealLanguage q 1 0)
    (hunit : ∀ i,L.weights i=1) (hform : PositiveTensorForm (L.matrices 0)) :
    L.problem.InFP := by
  obtain ⟨k,d,e,a,ρ,hk,ha,hρ,hform⟩ := hform
  have hp := TractableBlockComposition.source_rankOne_ising_tensor_inFP_of_ising
    hIsing L.field L.basis (L.matricesK 0) ⟨0,hk⟩ e a ha ρ hρ hform
  have hm : L.matricesK=fun _:Fin 1=>L.matricesK 0 := by
    funext l
    exact congrArg L.matricesK (Subsingleton.elim l 0)
  have hu : L.unariesK=(emptyUnaries : Fin 0→Fin q→L.field) := by funext l; exact l.elim0
  have hw : L.weightsK=fun _=>1 := by funext i; exact Subtype.ext (hunit i)
  change (evaluationProblem L.basis L.matricesK L.unariesK L.weightsK).InFP
  rw [hm,hu,hw]
  exact hp
theorem positiveTensorForm_of_quotient_data [Nonempty (Fin q)]
    (M : Matrix (Fin q) (Fin q) ℝ) (hpos : ∀ i j,0<M i j) (hs : ∀ i j,M i j=M j i)
    (hmom : ∀ r s : Quotient (Twins.rowSetoid (diagonalNormalize M)),∀ m : ℕ,
      Twins.quotientWeight (diagonalNormalize M) (fun i=>(M i i)^m) r=
        Twins.quotientWeight (diagonalNormalize M) (fun i=>(M i i)^m) s)
    (d : ℕ) (eQ : Quotient (Twins.rowSetoid (diagonalNormalize M))≃Boolean.Cube d)
    (ρ : Fin d→ℝ) (hρ : ∀ r,0<ρ r)
    (hcore : ∀ r s,Twins.quotientMatrix (diagonalNormalize M) (diagonalNormalize_symmetric M hs) r s=
      Boolean.tensor ρ (eQ r) (eQ s)) : PositiveTensorForm M := by
  obtain ⟨k,a,e,hk,ha,h⟩ := PositiveAmplitudeReconstruction.original_amplitude_tensor M hpos hs hmom eQ ρ hcore
  refine ⟨k,d,e,a,ρ,hk,ha,hρ,?_⟩
  ext i j
  simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.apply_symm_apply] using h (e.symm i) (e.symm j)
end PlanarHom.AlgebraicProductInterpolation.RealLanguage
