import PlanarHom.GraphParallelCode
import Mathlib.Algebra.BigOperators.Fin

/-! Exact partition semantics of occurrence-wise parallel thickening. -/

namespace PlanarHom.Complexity
noncomputable section
open Classical
open scoped BigOperators

/-- Occurrence replication raises each original factor to the replication
power, without deduplication or a simplicity assumption. -/
theorem prod_repeatWords {α R : Type} [Monoid R] (s : ℕ) (xs : List α) (f : α → R) :
    ((repeatWords s xs).map f).prod = (xs.map (fun x=>f x^s)).prod := by
  induction xs <;> simp_all [repeatWords_cons]

namespace GraphCode

/-- Extend an edge contribution to arbitrary endpoint pairs by the neutral
value outside the valid range. All actual graph occurrences use the first branch. -/
def edgeValue {C R : Type} [One R] (n : ℕ) (M : Matrix C C R)
    (σ : Fin n → C) (e : ℕ × ℕ) : R :=
  if h : e.1<n ∧ e.2<n then M (σ ⟨e.1,h.1⟩) (σ ⟨e.2,h.2⟩) else 1

/-- The finite edge-index product is precisely the product over the serialized
occurrence list. This retains loops and repeated endpoint pairs individually. -/
theorem evaluate_eq_list {C R : Type} [Fintype C] [CommSemiring R]
    (g : GraphCode) (hg : g.Valid) (M : Matrix C C R) (w : C → R) :
    g.evaluate hg M w = ∑ σ : Fin g.vertices → C,
      (∏ v, w (σ v)) * (g.edges.map (edgeValue g.vertices M σ)).prod := by
  classical
  unfold evaluate PlanarHom.MultiGraph.partition PlanarHom.MultiGraph.assignmentWeight
  refine Finset.sum_congr ?_ ?_
  · ext σ; simp
  intro σ _
  congr 1
  rw [←Fin.prod_univ_fun_getElem]
  apply Finset.prod_congr rfl
  intro e _
  have hv := hg (g.edges.get e) (List.get_mem _ _)
  simp only [toMultiGraph,edgeValue]
  simp only [List.get_eq_getElem] at hv
  simp only [List.get_eq_getElem, dif_pos hv]

/-- Replacing every occurrence by `s` parallel copies is exactly entrywise
`s`-th powering of the interaction matrix. Vertex weights are unchanged.
The statement includes loops, existing parallel occurrences, and `s = 0`. -/
theorem evaluate_parallel {C R : Type} [Fintype C] [CommSemiring R]
    (g : GraphCode) (hg : g.Valid) (s : ℕ) (M : Matrix C C R) (w : C → R) :
    (g.parallel s).evaluate (parallel_valid s g hg) M w =
      g.evaluate hg (fun i j=>M i j^s) w := by
  classical
  rw [evaluate_eq_list,evaluate_eq_list]
  change (∑ σ : Fin g.vertices → C, (∏ v,w (σ v)) *
      ((repeatWords s g.edges).map (edgeValue g.vertices M σ)).prod) = _
  refine Finset.sum_congr ?_ ?_
  · ext σ; simp
  intro σ _
  rw [prod_repeatWords]
  congr 2
  apply List.map_congr_left
  intro e he
  have hv := hg e he
  simp [edgeValue,hv]

end GraphCode
end
end PlanarHom.Complexity
