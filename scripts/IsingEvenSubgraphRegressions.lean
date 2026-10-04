import PlanarHom.IsingLoopRemoval
import PlanarHom.Tensor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Classical
namespace PlanarHom.IsingEvenSubgraphRegressions
open MultiGraph

/-- A source loop contributes two incidences, not one. -/
example (G : MultiGraph Unit Unit) : G.selectedDegree {()} () = 2 := by
  simp [selectedDegree]

/-- Removing a single source loop loses no vertex and gives exactly 2. -/
example (ρ : ℝ) (G : MultiGraph Unit Unit) :
    G.partition (Boolean.W ρ) (fun _ => 1) = 2 := by
  simp [partition, assignmentWeight, Boolean.W]

/-- Every isolated vertex supplies its own factor of two. -/
example {V E : Type*} [Fintype V] [Fintype E] (G : MultiGraph V E) (ρ : ℝ) :
    (G.disjointUnion isolatedVertex).partition (Boolean.W ρ) (fun _ => 1) =
      G.partition (Boolean.W ρ) (fun _ => 1) * 2 := by
  rw [partition_disjointUnion, partition_isolatedVertex]
  simp

/-- Two parallel occurrences remain two distinct selectable elements. -/
def parallelPair : MultiGraph Bool Bool := ⟨fun _ => false, fun _ => true⟩

example : parallelPair.selectedDegree {false} false = 1 := by
  simp [selectedDegree, parallelPair]

example : parallelPair.EvenSubgraph Finset.univ := by
  intro v
  cases v <;> norm_num [selectedDegree, parallelPair, Fintype.sum_bool]

example : ¬parallelPair.EvenSubgraph {false} := by
  intro h
  have := h false
  norm_num [selectedDegree, parallelPair] at this

/-- A three-cycle admits an odd-cardinality even edge set. -/
def triangle : MultiGraph (Fin 3) (Fin 3) := ⟨id, fun i => i + 1⟩

example : triangle.EvenSubgraph Finset.univ := by
  intro v
  fin_cases v <;>
    simp only [selectedDegree, Fin.sum_univ_succ, Fin.sum_univ_zero, triangle] <;>
    norm_num [Fin.add_def, Fin.ext_iff]

/-- At rho=3 the full triangle term is genuinely negative. -/
example : (∏ _e : Fin 3, ((1 - (3 : ℝ)) / (1 + 3))) = -(1 / 8 : ℝ) := by
  norm_num

end PlanarHom.IsingEvenSubgraphRegressions
