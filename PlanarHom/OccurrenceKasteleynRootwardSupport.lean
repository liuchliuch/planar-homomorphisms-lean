import PlanarHom.OccurrenceKasteleynLocalLaneFamily

/-! NEW exact support and entry-contact control for actual rootward steps.
These are the geometric induction invariants: one host disk and one parent
band are used, and every other band can be touched only at the input endpoint. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) {v : V} (H : HostFanChart F v)

theorem rootwardStep_range_subset (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1) (i : Fin n) :
    Set.range (C.rootwardStep H p n input i) ⊆
      {x | rayLength (x-d.drawing.point v)≤C.radius} ∪ Set.range (C.band Function.injective_id p.val.1) := by
  change Set.range ((C.rootwardDiskPath H p n input i).trans _) ⊆ _
  rw [Path.trans_range]
  rintro x (⟨t,ht⟩ | ⟨t,ht⟩)
  · left
    rw [← ht]
    exact C.hostDiskArc_radius_le H (outside_ne_reversedSlot (H.lower_lt_upper p) n i
      (height_outside_parent H (fun h => hout i (congrArg (fun a : HostDart G v => a.val.1) h)) (input i).2)) t
  · right
    rw [← ht]
    exact C.bandLane_mem_band _ _ _

theorem rootwardStep_contact_other_band (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (i : Fin n) (e : E) (hep : e≠p.val.1) (x : Plane)
    (hx : x∈Set.range (C.rootwardStep H p n input i))
    (hxe : x∈Set.range (C.band Function.injective_id e)) : x=C.port (input i).1.val (input i).2 := by
  change x∈Set.range ((C.rootwardDiskPath H p n input i).trans _) at hx
  rw [Path.trans_range] at hx
  rcases hx with ⟨s,hs⟩ | ⟨s,hs⟩
  · by_cases hs0 : s=0
    · subst s
      exact hs.symm.trans (C.rootwardDiskLane_zero H p n input i)
    by_cases hs1 : s=1
    · subst s
      have he : C.port p.val (H.slotParameter p n i)=x :=
        (C.rootwardDiskLane_one H p n input i).symm.trans hs
      exact False.elim (C.port_notMem_other_band hep.symm _ (he.symm ▸ hxe))
    have hne := outside_ne_reversedSlot (H.lower_lt_upper p) n i
      (height_outside_parent H (fun h => hout i (congrArg (fun a : HostDart G v => a.val.1) h)) (input i).2)
    exact False.elim (C.hostDiskArc_interior_notMem_band H hne s
      (PlaneDrawing.inside_of_ne_endpoints hs0 hs1) e (hs.symm ▸ hxe))
  · exact False.elim (Set.disjoint_left.mp (C.bandLane_disjoint_band hep.symm (H.slotParameter p n i))
      ⟨s,hs⟩ hxe)

theorem rootwardStep_ne_zero_avoids_other_band (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (i : Fin n) (e : E) (hep : e≠p.val.1) (t : I) (ht : t≠0) :
    C.rootwardStep H p n input i t∉Set.range (C.band Function.injective_id e) := by
  intro he
  have hh := C.rootwardStep_contact_other_band H p n input hout i e hep _ ⟨t,rfl⟩ he
  exact ht (C.rootwardStep_injective H p n input hout i (hh.trans (Path.source _).symm))

/-- Away from its entry host, a whole local step never enters a host disk.
This applies in particular to the fixed root during every non-root step. -/
theorem rootwardStep_radius_le (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (i : Fin n) (t : I) (w : V) (hvw : v≠w) :
    C.radius≤rayLength (C.rootwardStep H p n input i t-d.drawing.point w) := by
  have hx := C.rootwardStep_range_subset H p n input hout i (Set.mem_range_self t)
  rcases hx with hx | ⟨z,hz⟩
  · apply le_of_lt
    apply lt_of_not_ge
    intro hh
    exact Set.disjoint_left.mp (C.disks_disjoint v w hvw) hx hh
  · rw [← hz]
    exact C.band_radius_le Function.injective_id p.val.1 z w

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
