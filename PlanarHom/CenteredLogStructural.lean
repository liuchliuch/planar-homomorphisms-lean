import PlanarHom.CenteredLogStructuralForm
import PlanarHom.CenteredLogStructuralConverse
import PlanarHom.CenteredLogSourceRank

/-!
# Lemma 12.4: structural necessity, literal log rank, and algebraic converse

The structural implication and rank identity below hold for arbitrary real
entries. `tensor_form_inFP` supplies the converse for the original canonical
real-algebraic language. No identification of arbitrary-real computational
models with that exact number-field model is claimed here.
-/
noncomputable section
open Classical
namespace PlanarHom.CenteredLogStructural
open Boolean Structures CenteredLogTensorExpansion

/-- The full structural and centered-entrywise-log conclusion of source
Lemma 12.4, with the actual original q-color matrix throughout. -/
theorem lemma124_structure_and_rank {q : ℕ} [Nonempty (Fin q)]
    (M : Matrix (Fin q) (Fin q) ℝ) (w : Fin q → ℝ)
    (hs : ∀ i j, M i j = M j i) (hpos : ∀ i j, 0 < M i j)
    (hdiag : ∀ i j, M i i = M j j) (hrows : Function.Injective M)
    (hw : ∀ i, 0 < w i) (h : PositiveVertexWeightClass M w hs) :
    ∃ (d : ℕ) (e : Fin q ≃ Cube d) (γ μ : ℝ) (ρ : Fin d → ℝ),
      q = 2 ^ d ∧ 0 < γ ∧ 0 < μ ∧ (∀ r, 0 < ρ r ∧ ρ r ≠ 1) ∧
      (∀ i j, M i j = γ * tensor ρ (e i) (e j)) ∧ (∀ i, w i = μ) ∧
      (sourceCentering q * entrywiseLog M * sourceCentering q).rank = d := by
  obtain ⟨d, e, γ, μ, ρ, hγ, hμ, hρ, hM, hw'⟩ :=
    tensor_form_of_structural_membership M w hs hpos hdiag hrows hw h
  refine ⟨d, e, γ, μ, ρ, ?_, hγ, hμ, hρ, hM, hw', ?_⟩
  · simpa [Cube, Fintype.card_fun] using Fintype.card_congr e
  · exact source_centered_log_rank M e γ hγ ρ (fun r => (hρ r).1) (fun r => (hρ r).2) hM

end PlanarHom.CenteredLogStructural
