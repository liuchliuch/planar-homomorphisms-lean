import PlanarHom.RankOne
import PlanarHom.Tensor
import PlanarHom.Boolean

/-!
# Exact evaluations of the tractable positive forms

These are partition identities on arbitrary finite multigraphs. They do not
assert an FP bound or supply the planar Ising algorithm.
-/

open scoped BigOperators
open Classical
noncomputable section

namespace PlanarHom.MultiGraph

variable {V E I R : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq I] [CommSemiring R]

/-- Factor a finite family of independent interaction coordinates. -/
theorem unweighted_piInteraction (G : PlanarHom.MultiGraph V E) (C : I → Type*)
    [∀ i, Fintype (C i)] (M : ∀ i, Matrix (C i) (C i) R) :
    G.unweighted (fun x y : ∀ i, C i => ∏ i, M i (x i) (y i)) =
      ∏ i, G.unweighted (M i) := by
  simp only [unweighted_eq]
  calc
    (∑ σ : V → ∀ i, C i, ∏ e, ∏ i, M i (σ (G.src e) i) (σ (G.dst e) i)) =
        ∑ τ : ∀ i, V → C i, ∏ i, ∏ e, M i (τ i (G.src e)) (τ i (G.dst e)) := by
      apply Fintype.sum_equiv (Equiv.piComm (fun (_ : V) i => C i))
      intro σ
      exact Finset.prod_comm
    _ = ∏ i, ∑ τ : V → C i, ∏ e, M i (τ (G.src e)) (τ (G.dst e)) :=
      (Fintype.prod_sum (fun i (τ : V → C i) =>
        ∏ e, M i (τ (G.src e)) (τ (G.dst e)))).symm

/-- The partition function of a Boolean tensor is a product of Ising values. -/
theorem unweighted_booleanTensor (G : PlanarHom.MultiGraph V E) {d : ℕ}
    (ρ : Fin d → ℝ) :
    G.unweighted (PlanarHom.Boolean.tensor ρ) =
      ∏ i, G.unweighted (PlanarHom.Boolean.W (ρ i)) := by
  exact G.unweighted_piInteraction (fun _ : Fin d => Bool)
    (fun i => PlanarHom.Boolean.W (ρ i))

/-- Equation (11.7), the weighted positive-block evaluation formula.
It specializes to the positive-block part of Proposition 2.6. -/
theorem partition_rankOne_booleanTensor {C : Type*} [Fintype C]
    (G : PlanarHom.MultiGraph V E) (a weight : C → ℝ) {d : ℕ} (ρ : Fin d → ℝ) :
    G.partition
      (fun x y : C × PlanarHom.Boolean.Cube d =>
        a x.1 * a y.1 * PlanarHom.Boolean.tensor ρ x.2 y.2)
      (fun x => weight x.1) =
      (∏ v, ∑ i, weight i * a i ^ G.degree v) *
        ∏ j, G.unweighted (PlanarHom.Boolean.W (ρ j)) := by
  have hw : tensorVertexWeight weight (fun _ : PlanarHom.Boolean.Cube d => (1 : ℝ)) =
      (fun x : C × PlanarHom.Boolean.Cube d => weight x.1) := by
    funext x
    exact mul_one _
  rw [← hw]
  change G.partition (tensorInteraction (fun i j => a i * a j)
    (PlanarHom.Boolean.tensor ρ)) (tensorVertexWeight weight (fun _ => 1)) = _
  rw [G.partition_tensor, G.partition_rankOne]
  change (∏ v, ∑ i, weight i * a i ^ G.degree v) *
    G.unweighted (PlanarHom.Boolean.tensor ρ) = _
  rw [G.unweighted_booleanTensor]


end PlanarHom.MultiGraph
