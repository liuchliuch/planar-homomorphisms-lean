import PlanarHom.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Tensor products of interaction matrices

Equation (2.6) holds for every finite multigraph, not merely for planar graphs.
The proof below includes arbitrary vertex weights over any commutative semiring.
Color assignments into a product split into independent assignments into its two
factors, so both their contributions and their total partition functions factor.
-/

open scoped BigOperators
open Classical

namespace PlanarHom
namespace MultiGraph

variable {V E C D R : Type*}
variable [Fintype V] [Fintype E] [Fintype C] [Fintype D] [CommSemiring R]

/-- The entrywise description of the Kronecker (tensor) product. -/
def tensorInteraction (A : Matrix C C R) (B : Matrix D D R) :
    Matrix (C × D) (C × D) R :=
  fun i j => A i.1 j.1 * B i.2 j.2

/-- Product vertex weights on the product color domain. -/
def tensorVertexWeight (u : C → R) (v : D → R) : C × D → R :=
  fun i => u i.1 * v i.2

omit [Fintype C] [Fintype D] in
/-- An individual product-color assignment has a factored contribution. -/
theorem assignmentWeight_tensor (G : MultiGraph V E)
    (A : Matrix C C R) (B : Matrix D D R) (u : C → R) (v : D → R)
    (σ : V → C × D) :
    G.assignmentWeight (tensorInteraction A B) (tensorVertexWeight u v) σ =
      G.assignmentWeight A u (fun x => (σ x).1) *
        G.assignmentWeight B v (fun x => (σ x).2) := by
  simp only [assignmentWeight, tensorInteraction, tensorVertexWeight,
    Finset.prod_mul_distrib]
  ac_rfl

/-- Weighted tensor factorization, strengthening equation (2.6). -/
theorem partition_tensor (G : MultiGraph V E)
    (A : Matrix C C R) (B : Matrix D D R) (u : C → R) (v : D → R) :
    G.partition (tensorInteraction A B) (tensorVertexWeight u v) =
      G.partition A u * G.partition B v := by
  classical
  unfold partition
  calc
    (∑ σ : V → C × D,
        G.assignmentWeight (tensorInteraction A B) (tensorVertexWeight u v) σ) =
        ∑ p : (V → C) × (V → D),
          G.assignmentWeight A u p.1 * G.assignmentWeight B v p.2 := by
      apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow V (fun _ => C) (fun _ => D))
      intro σ
      exact assignmentWeight_tensor G A B u v σ
    _ = (∑ σ : V → C, G.assignmentWeight A u σ) *
        ∑ τ : V → D, G.assignmentWeight B v τ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp only [Finset.mul_sum]

/-- Equation (2.6): the unit-background partition function of a tensor product
is the product of the two unit-background partition functions. -/
theorem unweighted_tensor (G : MultiGraph V E)
    (A : Matrix C C R) (B : Matrix D D R) :
    G.unweighted (tensorInteraction A B) = G.unweighted A * G.unweighted B := by
  have h : tensorVertexWeight (fun _ : C => (1 : R)) (fun _ : D => 1) =
      (fun _ => 1) := by
    funext i
    exact one_mul 1
  unfold unweighted
  rw [← h]
  exact partition_tensor G A B (fun _ => 1) (fun _ => 1)

section DisjointUnion

variable {W F : Type*} [Fintype W] [Fintype F]

/-- Vertex-disjoint union, with tagged vertices and edges to preserve all
multiplicities, including loops and parallel edges. -/
def disjointUnion (G : MultiGraph V E) (H : MultiGraph W F) :
    MultiGraph (V ⊕ W) (E ⊕ F) where
  src := Sum.map G.src H.src
  dst := Sum.map G.dst H.dst

omit [Fintype C] in
/-- Assignment contributions factor over a vertex-disjoint graph union. -/
theorem assignmentWeight_disjointUnion (G : MultiGraph V E) (H : MultiGraph W F)
    (M : Matrix C C R) (w : C → R) (σ : V ⊕ W → C) :
    (G.disjointUnion H).assignmentWeight M w σ =
      G.assignmentWeight M w (fun x => σ (Sum.inl x)) *
        H.assignmentWeight M w (fun x => σ (Sum.inr x)) := by
  simp only [assignmentWeight, Fintype.prod_sum_type, disjointUnion,
    Sum.map_inl, Sum.map_inr]
  ac_rfl

/-- Weighted partition functions factor over vertex-disjoint graph unions. -/
theorem partition_disjointUnion (G : MultiGraph V E) (H : MultiGraph W F)
    (M : Matrix C C R) (w : C → R) :
    (G.disjointUnion H).partition M w = G.partition M w * H.partition M w := by
  classical
  letI : DecidableEq (V ⊕ W) := Classical.decEq (V ⊕ W)
  unfold partition
  calc
    (∑ σ : V ⊕ W → C, (G.disjointUnion H).assignmentWeight M w σ) =
        ∑ p : (V → C) × (W → C),
          G.assignmentWeight M w p.1 * H.assignmentWeight M w p.2 := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow V W C)
      intro σ
      exact assignmentWeight_disjointUnion G H M w σ
    _ = (∑ σ : V → C, G.assignmentWeight M w σ) *
        ∑ τ : W → C, H.assignmentWeight M w τ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp only [Finset.mul_sum]

/-- The same disjoint-union identity for unit vertex weights. -/
theorem unweighted_disjointUnion (G : MultiGraph V E) (H : MultiGraph W F)
    (M : Matrix C C R) :
    (G.disjointUnion H).unweighted M = G.unweighted M * H.unweighted M :=
  partition_disjointUnion G H M (fun _ => 1)

end DisjointUnion

end MultiGraph
end PlanarHom
