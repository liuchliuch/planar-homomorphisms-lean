import PlanarHom.OccurrenceKasteleynClippedRegions

/-! NEW exact exit-circle control. A whole local rootward step can meet any
other closed host disk only at its final port, on its actual opposite host. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I))

theorem bandLane_contact_external_disk (a : Dart E) (s t : I) (v : V)
    (ha : (G.dartPair a).1≠v) (ht : C.bandLane a s t∈C.hostDisk v) :
    t=1 ∧ (G.dartPair (a.1,!a.2)).1=v := by
  have he : rayLength (C.bandLane a s t-d.drawing.point v)=C.radius :=
    le_antisymm ht (C.band_radius_le Function.injective_id a.1 (outgoingParameter a.2 t,s) v)
  have hc := (C.band_on_circle_iff Function.injective_id a.1 (outgoingParameter a.2 t,s) v).mp he
  rcases a with ⟨e,b⟩
  cases b
  · simp only [dartPair,Bool.false_eq_true,if_false] at ha
    simp only [outgoingParameter,Bool.false_eq_true,if_false] at hc
    rcases hc with ⟨hh,hv⟩ | ⟨_,hv⟩
    · have hh' : t=1 := by simpa using congrArg unitInterval.symm hh
      exact ⟨hh',hv⟩
    · exact False.elim (ha hv)
  · simp only [dartPair,if_true] at ha
    simp only [outgoingParameter,if_true] at hc
    rcases hc with ⟨_,hv⟩ | ⟨hh,hv⟩
    · exact False.elim (ha hv)
    · exact ⟨hh,hv⟩

variable {v : V} (H : HostFanChart F v)

theorem rootwardStep_contact_external_disk (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (i : Fin n) (w : V) (hvw : v≠w) (x : Plane)
    (hx : x∈Set.range (C.rootwardStep H p n input i)) (hw : x∈C.hostDisk w) :
    x=C.port (p.val.1,!p.val.2) (H.slotParameter p n i) ∧
      (G.dartPair (p.val.1,!p.val.2)).1=w := by
  change x∈Set.range ((C.rootwardDiskPath H p n input i).trans _) at hx
  rw [Path.trans_range] at hx
  rcases hx with ⟨s,hs⟩ | ⟨s,hs⟩
  · have hv : x∈C.hostDisk v := by
      rw [← hs]
      exact C.hostDiskArc_radius_le H (outside_ne_reversedSlot (H.lower_lt_upper p) n i
        (height_outside_parent H (fun h => hout i (congrArg (fun a : HostDart G v => a.val.1) h)) _)) s
    exact False.elim (Set.disjoint_left.mp (C.disks_disjoint v w hvw) hv hw)
  · have hh := C.bandLane_contact_external_disk p.val (H.slotParameter p n i) s w
      (fun he => hvw (p.property.symm.trans he)) (hs.symm ▸ hw)
    refine ⟨?_,hh.2⟩
    rw [hh.1] at hs
    exact hs.symm.trans (C.bandLane_one _ _)

theorem rootwardStep_ne_one_outside (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (i : Fin n) (w : V) (hvw : v≠w) (t : I) (ht : t≠1) :
    C.radius<rayLength (C.rootwardStep H p n input i t-d.drawing.point w) := by
  apply lt_of_not_ge
  intro hw
  have hh := (C.rootwardStep_contact_external_disk H p n input hout i w hvw _ ⟨t,rfl⟩ hw).1
  exact ht (C.rootwardStep_injective H p n input hout i (hh.trans (Path.target _).symm))

theorem rootwardStep_disjoint_nonexit_disk (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (i : Fin n) (w : V) (hvw : v≠w) (hexit : (G.dartPair (p.val.1,!p.val.2)).1≠w) :
    Disjoint (Set.range (C.rootwardStep H p n input i)) (C.hostDisk w) := by
  apply Set.disjoint_left.mpr
  intro x hx hw
  exact hexit (C.rootwardStep_contact_external_disk H p n input hout i w hvw x hx hw).2

/-- If all earlier child traces avoid an external disk, the new joined path
has exactly the required possible final contact with that disk. -/
theorem joinedRootward_contact_external_disk (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I)
    (incoming : ∀ i, IncomingLane (C.port (input i).1.val (input i).2))
    (hout : ∀ i, (input i).1.val.1≠p.val.1)
    (w : V) (hvw : v≠w) (hold : ∀ i, Disjoint (incoming i).trace (C.hostDisk w))
    (i : Fin n) (x : Plane) (hx : x∈Set.range (C.joinedRootward H p n input incoming i))
    (hw : x∈C.hostDisk w) :
    x=C.port (p.val.1,!p.val.2) (H.slotParameter p n i) ∧
      (G.dartPair (p.val.1,!p.val.2)).1=w := by
  rw [C.joinedRootward_range] at hx
  rcases hx with hx | hx
  · exact False.elim (Set.disjoint_left.mp (hold i) hx hw)
  · exact C.rootwardStep_contact_external_disk H p n input hout i w hvw x hx hw

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
