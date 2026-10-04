import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic

/-!
# Finite multigraph partition functions

The paper's inputs allow loops and parallel edges. An explicit edge type preserves
multiplicity. The order of the endpoints is representational; reversing an edge
has no effect for a symmetric interaction. No planarity or complexity claim is
encoded by this foundation.
-/

open scoped BigOperators

noncomputable section

open Classical

namespace PlanarHom

/-- An incidence presentation of a finite undirected multigraph.
Different edge labels can have the same endpoints; equal endpoints are loops. -/
structure MultiGraph (V E : Type*) where
  src : E → V
  dst : E → V

namespace MultiGraph

variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C]
variable [CommSemiring R]

/-- The contribution of one color assignment, including fixed vertex weights. -/
def assignmentWeight (G : MultiGraph V E) (M : Matrix C C R) (w : C → R)
    (σ : V → C) : R :=
  (∏ v, w (σ v)) * ∏ e, M (σ (G.src e)) (σ (G.dst e))

/-- The weighted partition function (equation (2.2)). -/
def partition (G : MultiGraph V E) (M : Matrix C C R) (w : C → R) : R :=
  ∑ σ : V → C, G.assignmentWeight M w σ

/-- The unit-background partition function (equation (2.1)). -/
def unweighted (G : MultiGraph V E) (M : Matrix C C R) : R :=
  G.partition M (fun _ => 1)

omit [Fintype C] in
@[simp] theorem assignmentWeight_one (G : MultiGraph V E) (M : Matrix C C R)
    (σ : V → C) :
    G.assignmentWeight M (fun _ => 1) σ = ∏ e, M (σ (G.src e)) (σ (G.dst e)) := by
  simp [assignmentWeight]

theorem unweighted_eq (G : MultiGraph V E) (M : Matrix C C R) :
    G.unweighted M = ∑ σ : V → C, ∏ e, M (σ (G.src e)) (σ (G.dst e)) := by
  simp [unweighted, partition]

/-- Reversing every edge represents the same undirected multigraph. -/
def reverse (G : MultiGraph V E) : MultiGraph V E := ⟨G.dst, G.src⟩

theorem partition_reverse (G : MultiGraph V E) (M : Matrix C C R) (w : C → R)
    (hM : ∀ i j, M i j = M j i) :
    G.reverse.partition M w = G.partition M w := by
  unfold partition assignmentWeight
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact hM _ _

/-- Scaling every edge weight gives the scalar to the number of edges. -/
theorem partition_scale (G : MultiGraph V E) (M : Matrix C C R) (w : C → R) (c : R) :
    G.partition (fun i j => c * M i j) w =
      c ^ Fintype.card E * G.partition M w := by
  simp only [partition, assignmentWeight, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ac_rfl

/-- Edgeless graphs have independently summable colors at every vertex. -/
theorem partition_edgeless (G : MultiGraph V E) [IsEmpty E]
    (M : Matrix C C R) (w : C → R) :
    G.partition M w = (∑ i, w i) ^ Fintype.card V := by
  classical
  simp only [partition, assignmentWeight, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [← Fintype.prod_sum]
  simp

/-- Relabeling colors does not change the partition value. -/
theorem partition_reindexColors {D : Type*} [Fintype D]
    (G : MultiGraph V E) (M : Matrix D D R) (w : D → R) (e : C ≃ D) :
    G.partition (fun i j => M (e i) (e j)) (fun i => w (e i)) =
      G.partition M w := by
  classical
  let a : (V → C) ≃ (V → D) := Equiv.piCongrRight (fun _ => e)
  unfold partition
  apply Fintype.sum_equiv a
  intro σ
  rfl

/-- Every interaction equal to one leaves only independent vertex weights. -/
theorem partition_allOnes (G : MultiGraph V E) (w : C → R) :
    G.partition (fun _ _ => 1) w = (∑ i, w i) ^ Fintype.card V := by
  classical
  simp only [partition, assignmentWeight, Finset.prod_const_one, mul_one]
  rw [← Fintype.prod_sum]
  simp

/-- A zero interaction kills every assignment when an edge is present. -/
theorem partition_zero_of_nonempty_edges (G : MultiGraph V E) [Nonempty E] (w : C → R) :
    G.partition (fun _ _ => 0) w = 0 := by
  simp [partition, assignmentWeight, Fintype.card_ne_zero]

/-- Uniformly scaling background weights counts each vertex exactly once. -/
theorem partition_scale_vertexWeights (G : MultiGraph V E) (M : Matrix C C R)
    (w : C → R) (c : R) :
    G.partition M (fun i => c * w i) = c ^ Fintype.card V * G.partition M w := by
  simp only [partition, assignmentWeight, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ac_rfl

/-- The empty input multigraph. -/
def emptyGraph : MultiGraph Empty Empty := ⟨Empty.elim, Empty.elim⟩

/-- The unique empty assignment has weight one. -/
@[simp] theorem partition_emptyGraph (M : Matrix C C R) (w : C → R) :
    emptyGraph.partition M w = 1 := by
  simp [partition, assignmentWeight]

/-- A loopless isolated input vertex. -/
def isolatedVertex : MultiGraph PUnit Empty := ⟨Empty.elim, Empty.elim⟩

@[simp] theorem partition_isolatedVertex (M : Matrix C C R) (w : C → R) :
    isolatedVertex.partition M w = ∑ i, w i := by
  simpa using partition_edgeless isolatedVertex M w

end MultiGraph
end PlanarHom
