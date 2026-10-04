import PlanarHom.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Real.Basic

/-!
# Deletion of zero-weight colors

The exact finite-sum identity in Corollaries 11.2 and A.13. Applying the full
classification is supplied by the closed dichotomy endpoints.
-/

open scoped BigOperators
open Classical
noncomputable section

namespace PlanarHom.MultiGraph

variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C] [CommSemiring R]

/-- Restrict to any color set containing all nonzero vertex weights. -/
theorem partition_restrict_vertexWeights (G : PlanarHom.MultiGraph V E)
    (M : Matrix C C R) (w : C → R) (S : C → Prop)
    (hw : ∀ c, ¬ S c → w c = 0) :
    G.partition M w = G.partition (fun i j : {c // S c} => M i.1 j.1) (fun i => w i.1) := by
  classical
  let P : (V → C) → Prop := fun σ => ∀ v, S (σ v)
  have hbad : ∀ σ : {σ : V → C // ¬ P σ}, G.assignmentWeight M w σ.1 = 0 := by
    intro σ
    obtain ⟨v, hv⟩ : ∃ v, ¬ S (σ.1 v) := by simpa only [P, not_forall] using σ.2
    have hp : (∏ v, w (σ.1 v)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (hw _ hv)
    simp only [assignmentWeight, hp, zero_mul]
  unfold partition
  calc
    (∑ σ : V → C, G.assignmentWeight M w σ) =
        ∑ σ : {σ : V → C // P σ}, G.assignmentWeight M w σ.1 := by
      rw [← Fintype.sum_subtype_add_sum_subtype P (fun σ => G.assignmentWeight M w σ)]
      simp only [hbad, Finset.sum_const_zero, add_zero]
    _ = ∑ σ : V → {c // S c},
        G.assignmentWeight (fun i j : {c // S c} => M i.1 j.1) (fun i => w i.1) σ := by
      apply Fintype.sum_equiv (Equiv.subtypePiEquivPi (p := fun (_ : V) c => S c))
      intro σ
      rfl

/-- All-zero vertex weights give zero on every nonempty input. -/
theorem partition_zero_vertexWeights (G : PlanarHom.MultiGraph V E) [Nonempty V]
    (M : Matrix C C R) : G.partition M (fun _ => 0) = 0 := by
  simp [partition, assignmentWeight, Fintype.card_ne_zero]

/-- For nonnegative real vertex weights, exactly the positive-weight colors
may be retained, including when that subtype is empty. -/
theorem partition_restrict_positive_weights (G : PlanarHom.MultiGraph V E)
    (M : Matrix C C ℝ) (w : C → ℝ) (hw : ∀ c, 0 ≤ w c) :
    G.partition M w =
      G.partition (fun i j : {c // 0 < w c} => M i.1 j.1) (fun i => w i.1) := by
  apply G.partition_restrict_vertexWeights M w (fun c => 0 < w c)
  intro c hc
  exact le_antisymm (le_of_not_gt hc) (hw c)

end PlanarHom.MultiGraph
