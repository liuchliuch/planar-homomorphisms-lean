import PlanarHom.RootedColorRestriction
import PlanarHom.TypedSourceSideCoordinates

/-! Genuine homogeneous source-orientation semantics.  The hypotheses contain
only the source matrix, its numerical crossing property, and the input's
literal proper two-side assignment.  No source-availability hypothesis is used.
This file also covers singleton connected components with no edges. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.HomogeneousSourceOrientation
open Complexity Complexity.MixedCode PrescribedDomains
variable {C K : Type} [Fintype C] [Field K]

/-- On an edge, agreement of one endpoint of two proper Boolean colorings
forces agreement of the other endpoint. -/
theorem bool_agreement_across_edge {a b c d : Bool}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a = c) : b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | rfl | exact False.elim (hab rfl) | exact False.elim (hcd rfl) | cases hac

/-- A nonzero assignment has the prescribed source side at every vertex as
soon as it has the prescribed source side at one root. -/
theorem sides_eq_of_root_of_nonzero (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) (w : C → K)
    (side : C → Bool) (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j)
    (δ : Fin g.vertices → Bool)
    (hproper : ∀ u v, (GraphComponentCode.support g).Adj u v → δ u ≠ δ v)
    (σ : Fin g.vertices → C) (hr : side (σ r) = δ r)
    (h : (g.toMultiGraph hg).assignmentWeight M w σ ≠ 0) :
    ∀ v, side (σ v) = δ v := by
  intro v
  have hv := (SimpleGraph.reachable_iff_reflTransGen r v).mp (hc.preconnected r v)
  induction hv with
  | refl => exact hr
  | @tail u v _ huv ih =>
    exact bool_agreement_across_edge
      (hcross _ _ (RootedRestriction.assignment_adj_ne_zero g hg M hs w σ h u v huv))
      (hproper u v huv) ih

/-- Termwise orientation identity on connected support.  Zero assignment
weights need no side propagation and contribute zero on both sides. -/
theorem rootRestricted_eq_side_sum (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) (w : C → K)
    (side : C → Bool) (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j)
    (δ : Fin g.vertices → Bool)
    (hproper : ∀ u v, (GraphComponentCode.support g).Adj u v → δ u ≠ δ v) :
    (g.toMultiGraph hg).rootRestricted r M w {c | side c = δ r} =
      ∑ σ : Fin g.vertices → C, if (∀ v, side (σ v) = δ v) then
        (g.toMultiGraph hg).assignmentWeight M w σ else 0 := by
  unfold MultiGraph.rootRestricted
  apply Finset.sum_congr
  · ext σ; simp
  intro σ _
  by_cases hz : (g.toMultiGraph hg).assignmentWeight M w σ = 0
  · simp [hz]
  · have he : side (σ r) = δ r ↔ ∀ v, side (σ v) = δ v :=
      ⟨fun hr => sides_eq_of_root_of_nonzero g hg hc r M hs w side hcross δ hproper σ hr hz,
        fun ha => ha r⟩
    simp only [Set.mem_setOf_eq, he]

/-- The homogeneous mixed-code weight is literally the multigraph assignment
weight, before taking either unrestricted or restricted sums. -/
theorem homogeneous_assignmentWeight (g : MixedCode) (hg : g.Valid 1 0)
    (M : Matrix C C K) (w : C → K) (σ : Fin g.vertices → C) :
    (∏ v, w (σ v)) * (g.edges.map (binaryValue g.vertices 1 (fun _ => M) σ)).prod *
      (g.unaries.map (unaryValue g.vertices 0 (fun u => Fin.elim0 u) σ)).prod =
      (g.toMultiGraph hg).assignmentWeight M w σ := by
  rw [unaries_nil_of_valid_zero g hg]
  simp only [List.map_nil, List.prod_nil, mul_one]
  unfold MultiGraph.assignmentWeight
  congr 1
  rw [← Fin.prod_univ_fun_getElem]
  apply Finset.prod_congr rfl
  intro e _
  have hv := hg.1 (g.edges.get e) (List.get_mem _ _)
  simp only [List.get_eq_getElem] at hv
  simp only [binaryValue, dif_pos hv, toMultiGraph, List.get_eq_getElem]

/-- Literal prescribed-domain evaluation for the two side fibers is the
single-root restriction whenever the input side assignment is proper. -/
theorem evaluateRestricted_eq_rootRestricted (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) (w : C → K)
    (side : C → Bool) (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j)
    (δ : Fin g.vertices → Fin 2)
    (hproper : ∀ u v, (GraphComponentCode.support g).Adj u v →
      decide (δ u = 1) ≠ decide (δ v = 1)) :
    evaluateRestricted g hg (fun _ : Fin 1 => M) (fun u : Fin 0 => u.elim0) w
      (FixedRealRootRestrictions.Bipartite.domains side) δ =
      (g.toMultiGraph hg).rootRestricted r M w
        (FixedRealRootRestrictions.Bipartite.domains side (δ r)) := by
  change _ = (g.toMultiGraph hg).rootRestricted r M w {c | side c = decide (δ r = 1)}
  rw [rootRestricted_eq_side_sum g hg hc r M hs w side hcross _ hproper]
  unfold evaluateRestricted
  apply Finset.sum_congr
  · ext σ; simp
  intro σ _
  simp only [Allowed, FixedRealRootRestrictions.Bipartite.domains, Set.mem_setOf_eq,
    homogeneous_assignmentWeight g hg M w σ]

/-- Exact encoded-indicator semantics, preserving the original input's
intrinsic domain assignment and original homogeneous matrix and weights. -/
theorem evaluate_withDomains_eq_rootRestricted (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (GraphComponentCode.support g).Connected) (r : Fin g.vertices)
    (M : Matrix C C K) (hs : ∀ i j, M i j = M j i) (w : C → K)
    (side : C → Bool) (hcross : ∀ i j, M i j ≠ 0 → side i ≠ side j)
    (δ : Fin g.vertices → Fin 2)
    (hproper : ∀ u v, (GraphComponentCode.support g).Adj u v →
      decide (δ u = 1) ≠ decide (δ v = 1)) :
    (withDomains (unaryTypes := 0) g δ).evaluate (withDomains_valid g hg δ)
      (fun _ : Fin 1 => M)
      (extendedUnaries (fun u : Fin 0 => u.elim0)
        (FixedRealRootRestrictions.Bipartite.domains side)) w =
      (g.toMultiGraph hg).rootRestricted r M w
        (FixedRealRootRestrictions.Bipartite.domains side (δ r)) := by
  rw [evaluate_withDomains]
  exact evaluateRestricted_eq_rootRestricted g hg hc r M hs w side hcross δ hproper

end PlanarHom.HomogeneousSourceOrientation
