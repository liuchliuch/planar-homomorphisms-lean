import PlanarHom.FisherExpansionGraph
import PlanarHom.PlanarTransport

/-! NEW algebraic transport under literal vertex/occurrence bijections. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph.IncidenceEquiv
variable {V E W F : Type*} {G : MultiGraph V E} {H : MultiGraph W F}
variable (i : IncidenceEquiv G H)

 theorem selectedDegree_map (M : Finset E) (v : V) :
    H.selectedDegree (M.map i.edge.toEmbedding) (i.vertex v)=G.selectedDegree M v := by
  simp only [selectedDegree,Finset.sum_map,Equiv.toEmbedding_apply,i.src_eq,i.dst_eq,i.vertex.injective.eq_iff]

 theorem perfectMatching_map_iff (M : Finset E) :
    H.PerfectMatching (M.map i.edge.toEmbedding) ↔ G.PerfectMatching M := by
  constructor
  · intro h v
    rw [←i.selectedDegree_map M v]
    exact h _
  · intro h w
    obtain ⟨v,rfl⟩:=i.vertex.surjective w
    rw [i.selectedDegree_map]
    exact h v

 theorem evenSubgraph_map_iff (M : Finset E) :
    H.EvenSubgraph (M.map i.edge.toEmbedding) ↔ G.EvenSubgraph M := by
  constructor
  · intro h v
    rw [←i.selectedDegree_map M v]
    exact h _
  · intro h w
    obtain ⟨v,rfl⟩:=i.vertex.surjective w
    rw [i.selectedDegree_map]
    exact h v

 theorem degree_univ [Fintype E] [Fintype F] (v : V) :
    H.selectedDegree Finset.univ (i.vertex v)=G.selectedDegree Finset.univ v := by
  simpa using i.selectedDegree_map Finset.univ v

 theorem perfectMatchingSum [Fintype E] [Fintype F] (w : F→ℝ) :
    H.perfectMatchingSum w=G.perfectMatchingSum (w ∘ i.edge) := by
  unfold MultiGraph.perfectMatchingSum
  symm
  apply Fintype.sum_equiv (Equiv.finsetCongr i.edge)
  intro M
  change (if G.PerfectMatching M then _ else _)=(if H.PerfectMatching (M.map i.edge.toEmbedding) then _ else _)
  rw [i.perfectMatching_map_iff]
  split_ifs
  · simp [Finset.prod_map]
  · rfl

 theorem evenSubgraphSum [Fintype E] [Fintype F] (w : F→ℝ) :
    H.evenSubgraphSum w=G.evenSubgraphSum (w ∘ i.edge) := by
  unfold MultiGraph.evenSubgraphSum
  symm
  apply Fintype.sum_equiv (Equiv.finsetCongr i.edge)
  intro M
  change (if G.EvenSubgraph M then _ else _)=(if H.EvenSubgraph (M.map i.edge.toEmbedding) then _ else _)
  rw [i.evenSubgraph_map_iff]
  split_ifs
  · simp [Finset.prod_map]
  · rfl

end PlanarHom.MultiGraph.IncidenceEquiv
