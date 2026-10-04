import PlanarHom.ShortestPathWeights

/-!
# Distance-two shortest paths and common neighbors

A shortest path between vertices at graph distance two is determined by its
middle vertex. The equivalence here uses actual graph walks, and transfers
their cardinality directly to the set of common neighbors.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace PlanarHom.ShortestPathWeights

variable {V : Type*}

/-- At graph distance two, taking the middle vertex is a genuine equivalence
between shortest paths and common neighbors. -/
def shortestPathEquivCommonNeighbors (G : SimpleGraph V) {i j : V}
    (hd : G.dist i j = 2) :
    ShortestPath G i j ≃ {v : V // G.Adj i v ∧ G.Adj j v} := by
  unfold ShortestPath
  rw [hd]
  exact G.walkLengthTwoEquivCommonNeighbors i j

variable [Fintype V] [DecidableEq V]

/-- The shortest-path count at distance two equals the common-neighbor count. -/
theorem shortestPath_card_eq_commonNeighbors_card (G : SimpleGraph V) {i j : V}
    (hd : G.dist i j = 2) :
    Fintype.card (ShortestPath G i j) =
      Fintype.card {v : V // G.Adj i v ∧ G.Adj j v} := by
  classical
  exact Fintype.card_congr (shortestPathEquivCommonNeighbors G hd)

/-- Two genuine shortest paths at distance two give exactly two distinct
common neighbors. This is the combinatorial bridge to the Wheatstone argument. -/
theorem exists_two_commonNeighbors_of_shortestPath_card_two
    (G : SimpleGraph V) {i j : V} (hd : G.dist i j = 2)
    (hcard : Fintype.card (ShortestPath G i j) = 2) :
    ∃ u v : V, u ≠ v ∧
      ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v := by
  classical
  have hc : (Finset.univ.filter (fun a => G.Adj i a ∧ G.Adj j a)).card = 2 := by
    rw [← Fintype.card_subtype]
    exact (shortestPath_card_eq_commonNeighbors_card G hd).symm.trans hcard
  obtain ⟨u, v, huv, hset⟩ := Finset.card_eq_two.mp hc
  refine ⟨u, v, huv, fun a => ?_⟩
  have ha := congrArg (fun s : Finset V => a ∈ s) hset
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton] using Iff.of_eq ha

/-- A factorial shortest-path count specializes at distance two to the precise
two-common-neighbor hypothesis used in the Wheatstone obstruction. -/
theorem exists_two_commonNeighbors_of_shortestPath_card_factorial
    (G : SimpleGraph V) {i j : V} (hd : G.dist i j = 2)
    (hcard : Fintype.card (ShortestPath G i j) = (G.dist i j).factorial) :
    ∃ u v : V, u ≠ v ∧
      ∀ a, (G.Adj i a ∧ G.Adj j a) ↔ a = u ∨ a = v := by
  apply exists_two_commonNeighbors_of_shortestPath_card_two G hd
  simpa [hd] using hcard

end PlanarHom.ShortestPathWeights
