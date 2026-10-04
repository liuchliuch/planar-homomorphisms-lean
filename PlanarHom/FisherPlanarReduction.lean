import PlanarHom.FisherExpansionPlanarity
import PlanarHom.FisherCubicPlanarity

/-!
# The actual signed planar Fisher correspondence for arbitrary finite inputs

Both graph transformations and their ordinary-planarity witnesses are proved.
The choice of a suitable incidence order is existential and derived from the
given drawing. This module does not claim an effective embedding algorithm,
a Pfaffian orientation, a Pfaffian evaluation machine, or membership in FP.
-/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher
open MultiGraph
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

def fisherGraph (o : G.IncidenceOrdering) := cubicDecoration (expansionCubicPorts o)

def fisherWeight (o : G.IncidenceOrdering) (x : E → ℝ) :=
  cubicPolynomialWeight (expansionCubicPorts o) (expansionWeight o x)

theorem fisherGraph_planar (o : G.IncidenceOrdering) (h : (expansionGraph o).Planar) :
    (fisherGraph o).Planar := by
  apply cubicDecoration_planar
  simpa only [cubicOriginal_expansionCubicPorts] using h

/-- The order is chosen using geometry only, and then works for every signed
real weight assignment, including zero values. -/
theorem exists_planar_fisher (hG : G.Planar) :
    ∃ o : G.IncidenceOrdering, (fisherGraph o).Planar ∧
      ∀ x : E → ℝ, (fisherGraph o).perfectMatchingSum (fisherWeight o x) =
        (4 : ℝ) ^ Fintype.card V * G.evenSubgraphSum x := by
  obtain ⟨o,ho⟩ := exists_planar_expansion hG
  exact ⟨o, fisherGraph_planar o ho, arbitrary_fisher_polynomial o⟩

/-- Ordinary planar zero-field Ising reduces to the matching partition of a
concretely constructed planar occurrence graph, with every scalar proved. -/
theorem exists_planar_ising_matching (hG : G.Planar) (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    ∃ o : G.IncidenceOrdering, (fisherGraph o).Planar ∧
      G.partition (Boolean.W ρ) (fun _ => 1) =
        (((1 + ρ) / 2) ^ Fintype.card E / (2 : ℝ) ^ Fintype.card V) *
          (fisherGraph o).perfectMatchingSum (fisherWeight o (fun _ => (1-ρ)/(1+ρ))) := by
  obtain ⟨o,ho⟩ := exists_planar_expansion hG
  exact ⟨o, fisherGraph_planar o ho, arbitrary_ising_matching o ρ hρ⟩

/-- The final matching graph has exactly six vertices per original vertex or
edge occurrence. Its existence does not add a hidden exponential graph. -/
theorem fisherGraph_vertexCount (o : G.IncidenceOrdering) :
    Fintype.card (ExpansionVertex o × Fin 3) =
      6 * (Fintype.card E + Fintype.card V) := by
  rw [cubicDecoration_vertexCount, expansion_vertexCount]
  omega

theorem fisherGraph_edgeCount (o : G.IncidenceOrdering) :
    Fintype.card (ExpansionEdge o ⊕ (ExpansionVertex o × Fin 3)) =
      9 * (Fintype.card E + Fintype.card V) := by
  rw [cubicDecoration_edgeCount, expansion_edgeCount, expansion_vertexCount]
  omega

end PlanarHom.Fisher
