import PlanarHom.RotationFaceCutRegionCycles
import PlanarHom.OccurrenceMatchingCycleIncidence
import Mathlib.GroupTheory.Perm.Fin

/-! NEW two genuine boundary orbits of a simple occurrence cycle. The face cut
selects exactly one of them. This includes parallel two-edge cycles. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {root : Dart E}
variable (c : DirectedSimpleCycle G) (C : R.FaceCut c.cycleEdges root)

private theorem cycle_dart_mem (i : Fin c.length) : (c.dart i).1∈c.cycleEdges :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

 theorem forward_next_sameCycle (i : Fin c.length) :
    C.cutContour.SameCycle (c.dart i) (c.dart (cycleNext c.length c.length_ge_two i)) := by
  apply C.boundary_step_to_other _ _ (cycle_dart_mem c i) (cycle_dart_mem c _)
  · change (G.dartPair (c.dart _)).1=(G.dartPair ((c.dart i).1,!(c.dart i).2)).1
    rw [dartPair_reverse_fst,c.tail_eq,c.head_eq]
  · intro d hd hh
    rw [c.tail_eq] at hh
    exact c.incident_at_next i d hd hh

 theorem reverse_next_sameCycle (i : Fin c.length) :
    C.cutContour.SameCycle (reversePerm E (c.dart (cycleNext c.length c.length_ge_two i)))
      (reversePerm E (c.dart i)) := by
  apply C.boundary_step_to_other
    (reversePerm E (c.dart (cycleNext c.length c.length_ge_two i))) (reversePerm E (c.dart i))
    (by exact cycle_dart_mem c _) (by exact cycle_dart_mem c i)
  · change (G.dartPair ((c.dart i).1,!(c.dart i).2)).1=
      (G.dartPair (reversePerm E (reversePerm E (c.dart _)))).1
    rw [show reversePerm E (reversePerm E (c.dart _))=c.dart _ from (reversePerm E).symm_apply_apply _,
      dartPair_reverse_fst,c.head_eq,c.tail_eq]
  · intro d hd hh
    change (G.dartPair d).1=(G.dartPair ((c.dart i).1,!(c.dart i).2)).1 at hh
    rw [dartPair_reverse_fst,c.head_eq] at hh
    rcases c.incident_at_next i d hd hh with he|he
    · exact Or.inr he
    · left
      simpa only [reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta] using he

private theorem orbit_all_of_next (P : Equiv.Perm (Dart E)) (f : Fin c.length→Dart E)
    (hstep : ∀i,P.SameCycle (f i) (f (cycleNext c.length c.length_ge_two i)))
    (i j : Fin c.length) : P.SameCycle (f i) (f j) := by
  have hn : ∀i : Fin c.length,finRotate c.length i≠i := by
    intro i
    rw [←cycleNext_eq_finRotate c.length c.length_ge_two i]
    exact cycleNext_ne c.length c.length_ge_two i
  obtain ⟨n,hnat⟩ := ((isCycle_finRotate_of_le c.length_ge_two).sameCycle (hn i) (hn j)).exists_nat_pow_eq
  have hh : ∀n,P.SameCycle (f i) (f ((finRotate c.length)^[n] i)) := by
    intro n
    induction n with
    | zero => exact .rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply',←cycleNext_eq_finRotate c.length c.length_ge_two]
        exact ih.trans (hstep _)
  simpa only [Equiv.Perm.iterate_eq_pow,hnat] using hh n

 theorem forward_sameCycle (i j : Fin c.length) : C.cutContour.SameCycle (c.dart i) (c.dart j) :=
  orbit_all_of_next c C.cutContour c.dart (forward_next_sameCycle c C) i j

 theorem reverse_sameCycle (i j : Fin c.length) :
    C.cutContour.SameCycle (reversePerm E (c.dart i)) (reversePerm E (c.dart j)) :=
  orbit_all_of_next c C.cutContour (fun i=>reversePerm E (c.dart i))
    (fun i=>(reverse_next_sameCycle c C i).symm) i j

 theorem boundary_sameCycle_of_side (a b : Dart E) (ha : a.1∈c.cycleEdges) (hb : b.1∈c.cycleEdges)
    (hs : C.side a=C.side b) : C.cutContour.SameCycle a b := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hb
  rcases dart_eq_or_reverse_of_fst a (c.dart i) hi.symm with rfl|rfl <;>
    rcases dart_eq_or_reverse_of_fst b (c.dart j) hj.symm with rfl|rfl
  · exact forward_sameCycle c C i j
  · have he := C.side_eq_of_sameCycle (forward_sameCycle c C i j)
    have hx := C.crosses_dart (c.dart j)
    rw [decide_eq_true (cycle_dart_mem c j)] at hx
    change C.side (c.dart i)=C.side (reversePerm E (c.dart j)) at hs
    rw [←he,←hs] at hx
    simp at hx
  · have he := C.side_eq_of_sameCycle (forward_sameCycle c C i j)
    have hx := C.crosses_dart (c.dart i)
    rw [decide_eq_true (cycle_dart_mem c i)] at hx
    change C.side (reversePerm E (c.dart i))=C.side (c.dart j) at hs
    rw [hs,he] at hx
    simp at hx
  · exact reverse_sameCycle c C i j

 theorem count_selectedContour_simpleCycle
    (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v) :
    FinitePermutationCycles.count C.selectedContour=Fintype.card {v : V // C.InsideVertex v}+1 := by
  apply C.count_selectedContour
  · exact ⟨(c.dart ⟨0,by have := c.length_ge_two; omega⟩).1,cycle_dart_mem c _⟩
  · exact hinc
  · exact boundary_sameCycle_of_side c C

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
