import PlanarHom.OccurrenceAlternatingCycleWords
import PlanarHom.OccurrenceMatchingWordNodup
import PlanarHom.OccurrenceKasteleynMatchingSigns

/-! NEW literal occurrence partition realizing an alternating cycle flip as
an endpoint-word rotation, with the common matching occurrences retained. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn DirectedSimpleCycle
variable {V E : Type*} [LinearOrder V] {G : MultiGraph V E} {M N : Finset E}
namespace AlternatingCycleFlip

theorem leftDarts_edges (c : AlternatingCycleFlip G M N) (e : E) :
    e∈c.cycle.leftDarts.map Prod.fst ↔ e∈M ∧ e∈c.cycle.cycleEdges := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp h
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp ha
    have hk':k<c.cycle.length/2:=List.mem_range.mp hk
    have hi:2*k<c.cycle.length:=by have:=c.cycle.half_twice c.even_length; omega
    have hd:c.cycle.dartAt (2*k)=c.cycle.dart ⟨2*k,hi⟩:=by simp [dartAt,Nat.mod_eq_of_lt hi]
    rw [hd]
    exact ⟨(c.left_even _).mpr ⟨k,by dsimp; omega⟩,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩
  · rintro ⟨hM,hc⟩
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hc
    have he:Even i.val:=(c.left_even i).mp hM
    have hm:=Nat.even_iff.mp he
    have hk:i.val/2<c.cycle.length/2:=by have:=c.cycle.half_twice c.even_length; omega
    apply List.mem_map.mpr
    refine ⟨c.cycle.dartAt (2*(i.val/2)),List.mem_map.mpr ⟨i.val/2,List.mem_range.mpr hk,rfl⟩,?_⟩
    have hv:2*(i.val/2)=i.val:=by omega
    simp [dartAt,hv,Nat.mod_eq_of_lt i.isLt]

theorem rightDarts_edges (c : AlternatingCycleFlip G M N) (e : E) :
    e∈c.cycle.rightDarts.map Prod.fst ↔ e∈N ∧ e∈c.cycle.cycleEdges := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp h
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp ha
    have hk':k<c.cycle.length/2:=List.mem_range.mp hk
    have hi:2*k+1<c.cycle.length:=by have:=c.cycle.half_twice c.even_length; omega
    have hd:c.cycle.dartAt (2*k+1)=c.cycle.dart ⟨2*k+1,hi⟩:=by simp [dartAt,Nat.mod_eq_of_lt hi]
    rw [hd]
    exact ⟨(c.right_odd _).mpr ⟨k,rfl⟩,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩
  · rintro ⟨hN,hc⟩
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hc
    have he:Odd i.val:=(c.right_odd i).mp hN
    have hm:=Nat.odd_iff.mp he
    have hk:i.val/2<c.cycle.length/2:=by have:=c.cycle.half_twice c.even_length; omega
    apply List.mem_map.mpr
    refine ⟨c.cycle.dartAt (2*(i.val/2)+1),List.mem_map.mpr ⟨i.val/2,List.mem_range.mpr hk,rfl⟩,?_⟩
    have hv:2*(i.val/2)+1=i.val:=by omega
    simp [dartAt,hv,Nat.mod_eq_of_lt i.isLt]

def commonDarts (c : AlternatingCycleFlip G M N) : List (Dart E) :=
  (M\c.cycle.cycleEdges).toList.map (fun e=>(e,true))

theorem commonDarts_map (c : AlternatingCycleFlip G M N) :
    c.commonDarts.map Prod.fst=(M\c.cycle.cycleEdges).toList := by
  simp [commonDarts,List.map_map,Function.comp_def]

theorem agree_complement (c : AlternatingCycleFlip G M N) (e : E)
    (he : e∉c.cycle.cycleEdges) : e∈M ↔ e∈N := by
  apply c.agree_off e
  intro i hi
  exact he (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)

theorem left_common_edges (c : AlternatingCycleFlip G M N) :
    dartEdges (c.cycle.leftDarts++c.commonDarts)=M := by
  ext e
  simp only [dartEdges,List.mem_toFinset,List.map_append,List.mem_append,c.leftDarts_edges,
    c.commonDarts_map,Finset.mem_toList,Finset.mem_sdiff]
  tauto

theorem right_common_edges (c : AlternatingCycleFlip G M N) :
    dartEdges (c.cycle.rightDarts++c.commonDarts)=N := by
  ext e
  simp only [dartEdges,List.mem_toFinset,List.map_append,List.mem_append,c.rightDarts_edges,
    c.commonDarts_map,Finset.mem_toList,Finset.mem_sdiff]
  by_cases he:e∈c.cycle.cycleEdges
  · simp [he]
  · simp [he,c.agree_complement e he]

theorem left_right_edge_nodup (c : AlternatingCycleFlip G M N) :
    ((c.cycle.leftDarts++c.cycle.rightDarts).map Prod.fst).Nodup := by
  apply ((c.cycle.left_right_perm c.even_length).map Prod.fst).nodup_iff.mpr
  simpa only [cycleDarts,List.map_ofFn] using List.nodup_ofFn.mpr c.cycle.edge_injective

theorem left_common_edge_nodup (c : AlternatingCycleFlip G M N) :
    ((c.cycle.leftDarts++c.commonDarts).map Prod.fst).Nodup := by
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨?_,?_,?_⟩
  · exact (List.nodup_append.mp (by simpa only [List.map_append] using c.left_right_edge_nodup)).1
  · rw [c.commonDarts_map]
    exact Finset.nodup_toList _
  · intro e hl f hc hef
    subst f
    have he:=(c.leftDarts_edges e).mp hl
    rw [c.commonDarts_map] at hc
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hc)).2 he.2

theorem right_common_edge_nodup (c : AlternatingCycleFlip G M N) :
    ((c.cycle.rightDarts++c.commonDarts).map Prod.fst).Nodup := by
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨?_,?_,?_⟩
  · exact (List.nodup_append.mp (by simpa only [List.map_append] using c.left_right_edge_nodup)).2.1
  · rw [c.commonDarts_map]
    exact Finset.nodup_toList _
  · intro e hl f hc hef
    subst f
    have he:=(c.rightDarts_edges e).mp hl
    rw [c.commonDarts_map] at hc
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hc)).2 he.2

/-- Concrete cycle/common partition consumed by the literal matching-sign algebra. -/
def wordPartition (c : AlternatingCycleFlip G M N) : CycleFlipWordData G M N where
  left:=c.cycle.leftDarts
  right:=c.cycle.rightDarts
  common:=c.commonDarts
  first:=c.cycle.vertexAt 0
  rest:=c.cycle.restWord
  left_word:=c.cycle.left_word_cons c.even_length
  right_word:=c.cycle.right_word_append c.even_length
  left_nodup:=dartWord_nodup_of_matching c.left_perfect _ c.left_common_edge_nodup (by
    intro a ha
    rw [←c.left_common_edges]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩))
  right_nodup:=dartWord_nodup_of_matching c.right_perfect _ c.right_common_edge_nodup (by
    intro a ha
    rw [←c.right_common_edges]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩))
  left_edges:=c.left_common_edges
  right_edges:=c.right_common_edges

theorem wordPartition_cycle_perm (c : AlternatingCycleFlip G M N) :
    (c.wordPartition.left++c.wordPartition.right).Perm c.cycle.cycleDarts :=
  c.cycle.left_right_perm c.even_length

end AlternatingCycleFlip
end PlanarHom.MultiGraph
