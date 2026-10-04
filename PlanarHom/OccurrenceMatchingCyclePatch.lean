import PlanarHom.OccurrenceMatchingAlternatingCycle

/-! NEW actual alternating-cycle replacement and a strictly decreasing occurrence difference. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E} {M N : Finset E}

theorem selectedDegree_eq_of_incident_membership (S T : Finset E) (v : V)
    (hmem : ∀e,0<G.endpointCount e v→(e∈S ↔ e∈T)) : G.selectedDegree S v=G.selectedDegree T v := by
  have hs : (∑e∈S,G.endpointCount e v)=∑e∈S∪T,G.endpointCount e v := by
    apply Finset.sum_subset Finset.subset_union_left
    intro e he hn
    by_contra hz
    exact hn ((hmem e (Nat.pos_of_ne_zero hz)).mpr ((Finset.mem_union.mp he).resolve_left hn))
  have ht : (∑e∈T,G.endpointCount e v)=∑e∈S∪T,G.endpointCount e v := by
    apply Finset.sum_subset Finset.subset_union_right
    intro e he hn
    by_contra hz
    exact hn ((hmem e (Nat.pos_of_ne_zero hz)).mp ((Finset.mem_union.mp he).resolve_right hn))
  exact hs.trans ht.symm

namespace DirectedSimpleCycle

theorem incident_vertex_mem (c : DirectedSimpleCycle G) (e : E) (he : e∈c.cycleEdges)
    (v : V) (hv : 0<G.endpointCount e v) : v∈c.cycleVertices := by
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
  rw [endpointCount_dart,c.tail_eq,c.head_eq] at hv
  by_cases hi:c.vertex i=v
  · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
  · by_cases hj:c.vertex (cycleNext c.length c.length_ge_two i)=v
    · exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,hj⟩
    · simp only [if_neg hi,if_neg hj,zero_add,lt_self_iff_false] at hv

theorem even_coverage (c : DirectedSimpleCycle G) (heven : Even c.length) (S : Finset E)
    (hsel : ∀i,(c.dart i).1∈S ↔ Even i.val) :
    ∀i,(c.dart i).1∈S ∨ (c.dart (cycleNext c.length c.length_ge_two i)).1∈S := by
  intro i
  by_cases hi:Even i.val
  · exact Or.inl ((hsel i).mpr hi)
  · exact Or.inr ((hsel _).mpr ((cycleNext_even_iff _ _ heven i).mpr hi))

theorem odd_coverage (c : DirectedSimpleCycle G) (heven : Even c.length) (S : Finset E)
    (hsel : ∀i,(c.dart i).1∈S ↔ Odd i.val) :
    ∀i,(c.dart i).1∈S ∨ (c.dart (cycleNext c.length c.length_ge_two i)).1∈S := by
  intro i
  by_cases hi:Odd i.val
  · exact Or.inl ((hsel i).mpr hi)
  · apply Or.inr
    apply (hsel _).mpr
    have he : Even i.val := by rw [Nat.even_iff]; rw [Nat.odd_iff] at hi; omega
    have hn : ¬Even (cycleNext c.length c.length_ge_two i).val := by
      rw [cycleNext_even_iff _ _ heven i]
      exact not_not.mpr he
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at hn
    omega

theorem matching_incident_confined (c : DirectedSimpleCycle G) (S : Finset E) (hS : G.PerfectMatching S)
    (hsel : ∀i,(c.dart i).1∈S ∨ (c.dart (cycleNext c.length c.length_ge_two i)).1∈S)
    (v : V) (hv : v∈c.cycleVertices) (e : E) (he : e∈S) (hev : 0<G.endpointCount e v) : e∈c.cycleEdges := by
  obtain ⟨f,hf,hfc,hfv⟩:=c.incident_selected S hsel v hv
  have hh:=hS.eq_of_endpointCount_pos G he hf hev hfv
  exact hh.symm ▸ hfc

end DirectedSimpleCycle

namespace PerfectMatching
variable (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)
variable (c : DirectedSimpleCycle G) (heven : Even c.length)
variable (hleft : ∀i,(c.dart i).1∈M ↔ Even i.val) (hright : ∀i,(c.dart i).1∈N ↔ Odd i.val)

def patchCycle : Finset E := (M\c.cycleEdges) ∪ (N∩c.cycleEdges)

include hM hN heven hleft hright in
theorem patchCycle_perfect : G.PerfectMatching (patchCycle (M:=M) (N:=N) c) := by
  intro v
  by_cases hv:v∈c.cycleVertices
  · rw [selectedDegree_eq_of_incident_membership (patchCycle c) N v]
    · exact hN v
    · intro e hev
      constructor
      · intro he
        rcases Finset.mem_union.mp he with hm | hn
        · have hmc:=c.matching_incident_confined M hM (c.even_coverage heven M hleft) v hv e (Finset.mem_sdiff.mp hm).1 hev
          exact ((Finset.mem_sdiff.mp hm).2 hmc).elim
        · exact (Finset.mem_inter.mp hn).1
      · intro he
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he,
          c.matching_incident_confined N hN (c.odd_coverage heven N hright) v hv e he hev⟩)
  · rw [selectedDegree_eq_of_incident_membership (patchCycle c) M v]
    · exact hM v
    · intro e hev
      have hnot:e∉c.cycleEdges:=fun he=>hv (c.incident_vertex_mem e he v hev)
      simp [patchCycle,hnot]

def patchCycle_flip : AlternatingCycleFlip G M (patchCycle (M:=M) (N:=N) c) where
  cycle := c
  even_length := heven
  left_perfect := hM
  right_perfect := hM.patchCycle_perfect hN c heven hleft hright
  left_even := hleft
  right_odd := by
    intro i
    have hi:(c.dart i).1∈c.cycleEdges:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    simp only [patchCycle,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,hi,not_true_eq_false,and_false,false_or,and_true]
    exact hright i
  agree_off := by
    intro e he
    have hn:e∉c.cycleEdges:=by
      intro hm
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hm
      exact he i hi
    simp [patchCycle,hn]

include hleft hright in
theorem patchCycle_difference_card_lt : ((patchCycle (M:=M) (N:=N) c)\N).card<(M\N).card := by
  have hsub : patchCycle (M:=M) (N:=N) c\N ⊆ M\N := by
    intro e he
    have hh:=Finset.mem_sdiff.mp he
    rcases Finset.mem_union.mp hh.1 with hm | hn
    · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hm).1,hh.2⟩
    · exact (hh.2 (Finset.mem_inter.mp hn).1).elim
  let i:Fin c.length:=⟨0,by have:=c.length_ge_two; omega⟩
  have him:(c.dart i).1∈M:=(hleft i).mpr (by change Even 0; norm_num)
  have hin:(c.dart i).1∉N:=fun h=>by have hh:Odd 0:=(hright i).mp h; norm_num at hh
  have hic:(c.dart i).1∈c.cycleEdges:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hip:(c.dart i).1∉patchCycle (M:=M) (N:=N) c:=by simp [patchCycle,hic,hin]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro heq
  have hh:(c.dart i).1∈patchCycle (M:=M) (N:=N) c\N:=heq ▸ Finset.mem_sdiff.mpr ⟨him,hin⟩
  exact hip (Finset.mem_sdiff.mp hh).1

end PerfectMatching
end PlanarHom.MultiGraph
