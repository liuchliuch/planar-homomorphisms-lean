import PlanarHom.OccurrencePfaffianPairings
import PlanarHom.PottsRandomCluster
import Mathlib.SetTheory.Cardinal.Finite

/-! Degree-zero occurrence vertices are exactly singleton edgeless components. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
variable {V E : Type} [Fintype E]

 theorem degree_zero_iff_no_endpoints (G : MultiGraph V E) (v : V) :
    G.selectedDegree Finset.univ v=0 ↔ ∀e,G.src e≠v ∧ G.dst e≠v := by
  constructor
  · intro h e
    have he := Finset.single_le_sum (fun f (_ : f∈(Finset.univ : Finset E)) => Nat.zero_le (G.endpointCount f v)) (Finset.mem_univ e)
    change G.endpointCount e v≤G.selectedDegree Finset.univ v at he
    rw [h] at he
    constructor
    · intro hs
      simp [endpointCount,hs] at he
    · intro ht
      simp [endpointCount,ht] at he
  · intro h
    rw [selectedDegree_eq_sum_endpointCount]
    exact Finset.sum_eq_zero (fun e _ => by simp [endpointCount,(h e).1,(h e).2])

 theorem eq_of_connected_degree_zero (G : MultiGraph V E) (v : V)
    (hv : G.selectedDegree Finset.univ v=0) {w : V} (h : G.componentSetoid Finset.univ v w) : w=v := by
  have hn := (G.degree_zero_iff_no_endpoints v).mp hv
  have hc : G.EdgeConstant Finset.univ (fun u : V => u=v) := by
    intro e _
    exact propext ⟨fun h => ((hn e).1 h).elim,fun h => ((hn e).2 h).elim⟩
  have hh := G.edgeConstant_respects Finset.univ (fun u : V => u=v) hc h
  exact Eq.mp hh rfl

 theorem vertex_card_one_of_connected_empty [Fintype V] [Nonempty V] [IsEmpty E]
    (G : MultiGraph V E) (hc : ∀u v,G.componentSetoid Finset.univ u v) : Nat.card V=1 := by
  letI : Subsingleton V := ⟨by
    intro u v
    exact G.edgeConstant_respects Finset.univ id (fun e _ => isEmptyElim e) (hc u v)⟩
  exact Nat.card_unique
end PlanarHom.MultiGraph
