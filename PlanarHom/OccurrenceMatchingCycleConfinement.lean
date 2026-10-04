import PlanarHom.OccurrenceMatchingCycleIncidence

/-! NEW exact confinement of perfect matching incidences on an alternating cycle. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E} {M N : Finset E}

theorem cycleNext_surjective (n : ℕ) (hn : 2≤n) : Function.Surjective (cycleNext n hn) := by
  intro i
  obtain ⟨j,hj⟩:=(finRotate n).surjective i
  exact ⟨j,by rw [cycleNext_eq_finRotate]; exact hj⟩

theorem cycleNext_even_iff (n : ℕ) (hn : 2≤n) (heven : Even n) (i : Fin n) :
    Even (cycleNext n hn i).val ↔ ¬Even i.val := by
  have hnmod:=Nat.even_iff.mp heven
  by_cases hi:i.val+1<n
  · simp only [cycleNext,Nat.mod_eq_of_lt hi,Nat.even_iff]
    omega
  · have hh:i.val+1=n:=by omega
    have hodd : ¬Even i.val := by
      intro he
      have himod:=Nat.even_iff.mp he
      omega
    have hz : (cycleNext n hn i).val=0 := by simp only [cycleNext,hh,Nat.mod_self]
    rw [hz]
    exact iff_of_true (by norm_num) hodd

namespace DirectedSimpleCycle

theorem incident_selected (c : DirectedSimpleCycle G) (S : Finset E)
    (hsel : ∀i,(c.dart i).1∈S ∨ (c.dart (cycleNext c.length c.length_ge_two i)).1∈S)
    (v : V) (hv : v∈c.cycleVertices) :
    ∃e,e∈S ∧ e∈c.cycleEdges ∧ 0<G.endpointCount e v := by
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hv
  obtain ⟨j,hj⟩:=cycleNext_surjective c.length c.length_ge_two i
  have hvertex : c.vertex (cycleNext c.length c.length_ge_two j)=v := (congrArg c.vertex hj).trans hi
  rcases hsel j with hs | hs
  · refine ⟨(c.dart j).1,hs,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
    rw [endpointCount_dart,c.head_eq,hvertex]
    simp
  · refine ⟨(c.dart (cycleNext c.length c.length_ge_two j)).1,hs,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,?_⟩
    rw [endpointCount_dart,c.tail_eq,hvertex]
    simp

end DirectedSimpleCycle
namespace AlternatingCycleFlip

theorem left_cycle_incident (c : AlternatingCycleFlip G M N) (v : V) (hv : v∈c.cycle.cycleVertices) :
    ∃e,e∈M ∧ e∈c.cycle.cycleEdges ∧ 0<G.endpointCount e v := by
  apply c.cycle.incident_selected M _ v hv
  intro i
  by_cases hi:Even i.val
  · exact Or.inl ((c.left_even i).mpr hi)
  · exact Or.inr ((c.left_even _).mpr ((cycleNext_even_iff _ _ c.even_length i).mpr hi))

theorem right_cycle_incident (c : AlternatingCycleFlip G M N) (v : V) (hv : v∈c.cycle.cycleVertices) :
    ∃e,e∈N ∧ e∈c.cycle.cycleEdges ∧ 0<G.endpointCount e v := by
  apply c.cycle.incident_selected N _ v hv
  intro i
  by_cases hi:Odd i.val
  · exact Or.inl ((c.right_odd i).mpr hi)
  · apply Or.inr
    apply (c.right_odd _).mpr
    have he : Even i.val := by rw [Nat.even_iff]; rw [Nat.odd_iff] at hi; omega
    have hn : ¬Even (cycleNext c.cycle.length c.cycle.length_ge_two i).val := by
      rw [cycleNext_even_iff _ _ c.even_length i]
      exact not_not.mpr he
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at hn
    omega

theorem left_incident_mem_cycle (c : AlternatingCycleFlip G M N) (v : V)
    (hv : v∈c.cycle.cycleVertices) (e : E) (he : e∈M) (hev : 0<G.endpointCount e v) :
    e∈c.cycle.cycleEdges := by
  obtain ⟨f,hf,hfc,hfv⟩:=c.left_cycle_incident v hv
  have hh:=c.left_perfect.eq_of_endpointCount_pos G he hf hev hfv
  exact hh.symm ▸ hfc

theorem right_incident_mem_cycle (c : AlternatingCycleFlip G M N) (v : V)
    (hv : v∈c.cycle.cycleVertices) (e : E) (he : e∈N) (hev : 0<G.endpointCount e v) :
    e∈c.cycle.cycleEdges := by
  obtain ⟨f,hf,hfc,hfv⟩:=c.right_cycle_incident v hv
  have hh:=c.right_perfect.eq_of_endpointCount_pos G he hf hev hfv
  exact hh.symm ▸ hfc

end AlternatingCycleFlip
end PlanarHom.MultiGraph
