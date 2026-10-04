import PlanarHom.OccurrenceMatchingCycleIncidence
import PlanarHom.RotationFaceCutSigns

/-! NEW self-contained matching confinement. The finite region-cardinality
proof is restored verbatim from recovered OccurrenceKasteleynMatchingParity;
its missing geometric imports are replaced by actual finite face-cut facts. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*}

/-- A selected matching cannot leave a vertex region if both endpoints of every
selected occurrence have the same membership in that region. -/
theorem PerfectMatching.region_card_even (G : MultiGraph V E) {M : Finset E}
    (hM : G.PerfectMatching M) (S : Finset V)
    (hclosed : ∀ e ∈ M, G.src e ∈ S ↔ G.dst e ∈ S) : Even S.card := by
  have hdegree : ∀ v, G.selectedDegree M v = 1 := hM
  have hcard : S.card = 2 * (M.filter (fun e => G.src e ∈ S)).card := by
    calc
      S.card = ∑ v ∈ S, G.selectedDegree M v := by simp [hdegree]
      _ = ∑ e ∈ M, ((if G.src e ∈ S then 1 else 0) +
          (if G.dst e ∈ S then 1 else 0) : Nat) := by
        unfold selectedDegree
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e he
        simp [Finset.sum_add_distrib]
      _ = 2 * (M.filter (fun e => G.src e ∈ S)).card := by
        simp only [Finset.card_filter,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hs : G.src e ∈ S
        · have hd := (hclosed e he).mp hs
          simp [hs,hd]
        · have hd : G.dst e ∉ S := fun h => hs ((hclosed e he).mpr h)
          simp [hs,hd]
  exact ⟨(M.filter (fun e => G.src e ∈ S)).card,by omega⟩


theorem PerfectMatching.exists_dart_at {G : MultiGraph V E} {M : Finset E}
    (hM : G.PerfectMatching M) (v : V) : ∃a : Dart E,(G.dartPair a).1=v := by
  by_contra hn
  have hs : ∀e : E,G.src e≠v := fun e h=>hn ⟨(e,true),h⟩
  have ht : ∀e : E,G.dst e≠v := fun e h=>hn ⟨(e,false),h⟩
  have h := hM v
  simp [selectedDegree,hs,ht] at h

namespace DirectedSimpleCycle
variable {G : MultiGraph V E}
theorem vertex_mem_of_incident (c : DirectedSimpleCycle G) (a : Dart E) (ha : a.1∈c.cycleEdges) :
    (G.dartPair a).1∈c.cycleVertices := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
  rcases dart_eq_or_reverse_of_fst a (c.dart i) hi.symm with rfl|rfl
  · rw [c.tail_eq]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · rw [dartPair_reverse_fst,c.head_eq]
    exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
end DirectedSimpleCycle
end PlanarHom.MultiGraph

namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {root : Dart E}
variable (c : DirectedSimpleCycle G) (C : R.FaceCut c.cycleEdges root)

 theorem matching_inside_closed {M : Finset E}
    (htouch : ∀e∈M,G.src e∈c.cycleVertices ∨ G.dst e∈c.cycleVertices → e∈c.cycleEdges)
    (e : E) (he : e∈M) : C.InsideVertex (G.src e) ↔ C.InsideVertex (G.dst e) := by
  by_cases hb : e∈c.cycleEdges
  · have hs : ¬C.InsideVertex (G.src e) := fun h=>(C.inside_excludes_boundary h (e,true) rfl) hb
    have ht : ¬C.InsideVertex (G.dst e) := fun h=>(C.inside_excludes_boundary h (e,false) rfl) hb
    simp [hs,ht]
  · apply C.inside_iff_across_nonboundary e hb
    · intro a ha hm
      apply hb
      apply htouch e he
      left
      exact ha ▸ c.vertex_mem_of_incident a hm
    · intro a ha hm
      apply hb
      apply htouch e he
      right
      exact ha ▸ c.vertex_mem_of_incident a hm

 theorem inside_card_even_of_matching {M : Finset E} (hM : G.PerfectMatching M)
    (htouch : ∀e∈M,G.src e∈c.cycleVertices ∨ G.dst e∈c.cycleVertices → e∈c.cycleEdges) :
    Even (Fintype.card {v : V // C.InsideVertex v}) := by
  have h := hM.region_card_even G (Finset.univ.filter C.InsideVertex) (by
    intro e he
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact matching_inside_closed c C htouch e he)
  simpa only [Fintype.card_subtype] using h

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
