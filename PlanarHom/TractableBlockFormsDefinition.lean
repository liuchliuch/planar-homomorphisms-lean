import PlanarHom.TractableBlockComposition
import PlanarHom.BipartiteRankTwoMatrix

/-! Exact recovered literal block predicate, separated from its algorithmic
proof so structural transport does not depend on an unfinished evaluator. -/
noncomputable section
namespace PlanarHom.TractableBlockComposition
/-- Precisely the three source forms: singleton zero, positive rank-one tensor,
and positive bipartite rank-two tensor. Empty Ising tensors and rho=1 are allowed. -/
inductive Form {C : Type} (M : Matrix C C ℝ) : Prop
  | zero (e : C ≃ Fin 1) (hzero : M = 0)
  | rankOne {k d : ℕ} (i0 : Fin k) (e : C ≃ (Fin k × Boolean.Cube d))
      (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (ρ : Fin d → ℝ) (hρ : ∀ i, 0 < ρ i)
      (hsource : Matrix.reindex e e M =
        fun p r => a p.1 * a r.1 * Boolean.tensor ρ p.2 r.2)
  | bipartite {k l d : ℕ} (i0 : Fin k) (j0 : Fin l)
      (e : C ≃ ((Fin k ⊕ Fin l) × Boolean.Cube d))
      (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (b : Fin l → ℝ) (hb : ∀ i, 0 < b i)
      (ρ : Fin d → ℝ) (hρ : ∀ i, 0 < ρ i)
      (hsource : Matrix.reindex e e M =
        MultiGraph.tensorInteraction (BipartiteRankTwoTractability.matrix a b) (Boolean.tensor ρ))

end PlanarHom.TractableBlockComposition
