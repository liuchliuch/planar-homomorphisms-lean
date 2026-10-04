import PlanarHom.SurfaceCycleBoundaryFamily
import PlanarHom.RotationSimpleCycleCut

/-! NEW boundary-orbit control for a disjoint union of actual simple cycles.
The selected side follows exactly one directed orbit of each component. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {root : Dart E} {A : Finset E} {n : ℕ}
variable (F : CycleBoundaryFamily G A n) (C : R.FaceCut A root)

theorem family_forward_next (i : Fin n) (j : Fin (F.cycle i).length) :
    C.cutContour.SameCycle ((F.cycle i).dart j)
      ((F.cycle i).dart (cycleNext _ (F.cycle i).length_ge_two j)) := by
  apply C.boundary_step_to_other _ _ (F.cycle_dart_mem i j) (F.cycle_dart_mem i _)
  · change (G.dartPair ((F.cycle i).dart _)).1=(G.dartPair (((F.cycle i).dart j).1,!((F.cycle i).dart j).2)).1
    rw [dartPair_reverse_fst,(F.cycle i).tail_eq,(F.cycle i).head_eq]
  · intro d hd hh
    rw [(F.cycle i).tail_eq] at hh
    exact F.selected_incident_at_next i j d hd hh

theorem family_reverse_next (i : Fin n) (j : Fin (F.cycle i).length) :
    C.cutContour.SameCycle (reversePerm E ((F.cycle i).dart (cycleNext _ (F.cycle i).length_ge_two j)))
      (reversePerm E ((F.cycle i).dart j)) := by
  apply C.boundary_step_to_other
    (reversePerm E ((F.cycle i).dart (cycleNext _ (F.cycle i).length_ge_two j)))
    (reversePerm E ((F.cycle i).dart j))
    (by exact F.cycle_dart_mem i _) (by exact F.cycle_dart_mem i j)
  · change (G.dartPair (((F.cycle i).dart j).1,!((F.cycle i).dart j).2)).1=
      (G.dartPair (reversePerm E (reversePerm E ((F.cycle i).dart _)))).1
    rw [show reversePerm E (reversePerm E ((F.cycle i).dart _))=(F.cycle i).dart _ from (reversePerm E).symm_apply_apply _,
      dartPair_reverse_fst,(F.cycle i).head_eq,(F.cycle i).tail_eq]
  · intro d hd hh
    change (G.dartPair d).1=(G.dartPair (((F.cycle i).dart j).1,!((F.cycle i).dart j).2)).1 at hh
    rw [dartPair_reverse_fst,(F.cycle i).head_eq] at hh
    rcases F.selected_incident_at_next i j d hd hh with he|he
    · exact Or.inr he
    · left
      simpa only [reversePerm,Equiv.coe_fn_mk,Bool.not_not,Prod.mk.eta] using he

private theorem orbit_all_of_successor {k : ℕ} (hk : 2≤k) (P : Equiv.Perm (Dart E))
    (f : Fin k→Dart E) (hstep : ∀j,P.SameCycle (f j) (f (cycleNext k hk j)))
    (j l : Fin k) : P.SameCycle (f j) (f l) := by
  have hn : ∀j : Fin k,finRotate k j≠j := by
    intro j
    rw [←cycleNext_eq_finRotate k hk j]
    exact cycleNext_ne k hk j
  obtain ⟨r,hr⟩:=((isCycle_finRotate_of_le hk).sameCycle (hn j) (hn l)).exists_nat_pow_eq
  have hh : ∀r,P.SameCycle (f j) (f ((finRotate k)^[r] j)) := by
    intro r
    induction r with
    | zero => exact .rfl
    | succ r ih =>
      rw [Function.iterate_succ_apply',←cycleNext_eq_finRotate k hk]
      exact ih.trans (hstep _)
  simpa only [Equiv.Perm.iterate_eq_pow,hr] using hh r

theorem family_forward_sameCycle (i : Fin n) (j l : Fin (F.cycle i).length) :
    C.cutContour.SameCycle ((F.cycle i).dart j) ((F.cycle i).dart l) :=
  orbit_all_of_successor (F.cycle i).length_ge_two C.cutContour (F.cycle i).dart (family_forward_next F C i) j l

theorem family_reverse_sameCycle (i : Fin n) (j l : Fin (F.cycle i).length) :
    C.cutContour.SameCycle (reversePerm E ((F.cycle i).dart j)) (reversePerm E ((F.cycle i).dart l)) :=
  orbit_all_of_successor (F.cycle i).length_ge_two C.cutContour
    (fun j=>reversePerm E ((F.cycle i).dart j)) (fun j=>(family_reverse_next F C i j).symm) j l

theorem family_boundary_sameCycle_of_side (i : Fin n) (a b : Dart E)
    (ha : a.1∈(F.cycle i).cycleEdges) (hb : b.1∈(F.cycle i).cycleEdges)
    (hs : C.side a=C.side b) : C.cutContour.SameCycle a b := by
  obtain ⟨j,_,hj⟩:=Finset.mem_image.mp ha
  obtain ⟨l,_,hl⟩:=Finset.mem_image.mp hb
  rcases dart_eq_or_reverse_of_fst a ((F.cycle i).dart j) hj.symm with rfl|rfl <;>
    rcases dart_eq_or_reverse_of_fst b ((F.cycle i).dart l) hl.symm with rfl|rfl
  · exact family_forward_sameCycle F C i j l
  · have he:=C.side_eq_of_sameCycle (family_forward_sameCycle F C i j l)
    have hx:=C.crosses_dart ((F.cycle i).dart l)
    rw [decide_eq_true (F.cycle_dart_mem i l)] at hx
    change C.side ((F.cycle i).dart j)=C.side (reversePerm E ((F.cycle i).dart l)) at hs
    rw [←he,←hs] at hx
    simp at hx
  · have he:=C.side_eq_of_sameCycle (family_forward_sameCycle F C i j l)
    have hx:=C.crosses_dart ((F.cycle i).dart j)
    rw [decide_eq_true (F.cycle_dart_mem i j)] at hx
    change C.side (reversePerm E ((F.cycle i).dart j))=C.side ((F.cycle i).dart l) at hs
    rw [hs,he] at hx
    simp at hx
  · exact family_reverse_sameCycle F C i j l

theorem family_host_step (i : Fin n) (a : Dart E)
    (ha : (G.dartPair a).1∈(F.cycle i).cycleVertices) :
    (G.dartPair (C.cutContour a)).1∈(F.cycle i).cycleVertices := by
  by_cases he:a.1∈A
  · rw [C.cutContour_boundary a he,R.facePerm_host]
    exact (F.cycle i).vertex_mem_of_incident (reversePerm E a) (F.incident_cycle_edge i a he ha)
  · rw [C.cutContour_nonboundary a he,R.rotation_host]
    exact ha

theorem family_host_sameCycle (i : Fin n) (a b : Dart E)
    (ha : (G.dartPair a).1∈(F.cycle i).cycleVertices) (hab : C.cutContour.SameCycle a b) :
    (G.dartPair b).1∈(F.cycle i).cycleVertices := by
  obtain ⟨k,hk⟩:=hab.exists_nat_pow_eq
  have hi : ∀k,(G.dartPair (C.cutContour^[k] a)).1∈(F.cycle i).cycleVertices := by
    intro k
    induction k with
    | zero => exact ha
    | succ k ih => rw [Function.iterate_succ_apply']; exact family_host_step F C i _ ih
  simpa only [Equiv.Perm.iterate_eq_pow,hk] using hi k

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
