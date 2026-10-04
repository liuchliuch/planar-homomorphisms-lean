import PlanarHom.FisherExpansionCorrespondence

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.FisherArbitraryRegressions
open MultiGraph Fisher

/-- Cubicization is proved from actual degrees for every finite input. -/
example {V E : Type*} [Fintype V] [Fintype E] (G : MultiGraph V E)
    (o : G.IncidenceOrdering) (q : ExpansionVertex o) :
    (expansionGraph o).selectedDegree Finset.univ q = 3 := expansion_is_cubic o q

/-- The zero-weight boundary case counts precisely the independent new loops. -/
example {V E : Type*} [Fintype V] [Fintype E] (G : MultiGraph V E)
    (o : G.IncidenceOrdering) :
    (cubicDecoration (expansionCubicPorts o)).perfectMatchingSum
      (cubicPolynomialWeight (expansionCubicPorts o) (expansionWeight o (fun _ => 0))) =
        (4 : ℝ) ^ Fintype.card V := by
  rw [arbitrary_fisher_polynomial, evenSubgraphSum_zero, mul_one]

def oneLoop : MultiGraph Unit Unit := ⟨fun _ => (), fun _ => ()⟩

/-- A negative Ising expansion parameter on an actual source loop gives the
correct literal matching sum, with both endpoint occurrences retained. -/
example (o : oneLoop.IncidenceOrdering) :
    (cubicDecoration (expansionCubicPorts o)).perfectMatchingSum
      (cubicPolynomialWeight (expansionCubicPorts o)
        (expansionWeight o (fun _ => -(1 / 2 : ℝ)))) = 2 := by
  have h := arbitrary_ising_matching o 3 (by norm_num)
  norm_num [oneLoop, MultiGraph.partition, MultiGraph.assignmentWeight, Boolean.W] at h
  exact h.symm

/-- A single isolated source vertex is represented by two cubic vertices. -/
example (o : isolatedVertex.IncidenceOrdering) : Fintype.card (ExpansionVertex o) = 2 := by
  rw [expansion_vertexCount]
  norm_num

/-- Its three expanded edge occurrences are a bridge and two separate loops. -/
example (o : isolatedVertex.IncidenceOrdering) : Fintype.card (ExpansionEdge o) = 3 := by
  rw [expansion_edgeCount]
  norm_num

end PlanarHom.FisherArbitraryRegressions
