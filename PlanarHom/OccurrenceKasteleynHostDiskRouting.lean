import PlanarHom.OccurrenceKasteleynFanCoordinates
import PlanarHom.OccurrenceKasteleynCircleCorners
import PlanarHom.RadialPottsAssemblyCircleArches

/-! NEW literal local rootward routing in the actual disjoint host disks.
Every route joins an incident input port to a constructed interior parent-fan
slot. The only ordering input is the finite numeric scan supplied by local rows;
the paths, slots, separation and containment are all constructed and proved. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) {v : V} (H : HostFanChart F v)

private theorem diskMap_boundary_rayLength (x : ℝ) : rayLength (diskMap (0,x))=1 := by
  unfold rayLength
  rw [diskMap_boundary]
  norm_num

theorem hostCircleMap_rayLength (q : Plane) :
    rayLength (C.hostCircleMap H q-d.drawing.point v)=C.radius*rayLength q := by
  change rayLength ((d.drawing.point v+C.radius • CirclePoleChart.unrotate H.pole q)-d.drawing.point v)=_
  rw [add_sub_cancel_left,rayLength_smul,abs_of_pos C.radius_pos,
    CirclePoleChart.unrotate_rayLength H.pole_circle]

/-- Explicit rotated, scaled Cayley parabola in the actual host disk. -/
def hostDiskArc (x y : ℝ) : C(I,Plane) :=
  (C.hostCircleMap H).comp (diskArch x y)

@[simp] theorem hostDiskArc_zero (x y : ℝ) :
    C.hostDiskArc H x y 0=C.hostCircleMap H (diskMap (0,x)) := by
  change C.hostCircleMap H (diskArch x y 0)=_
  rw [diskArch_zero]

@[simp] theorem hostDiskArc_one (x y : ℝ) :
    C.hostDiskArc H x y 1=C.hostCircleMap H (diskMap (0,y)) := by
  change C.hostCircleMap H (diskArch x y 1)=_
  rw [diskArch_one]

theorem hostDiskArc_injective {x y : ℝ} (hxy : x≠y) :
    Function.Injective (C.hostDiskArc H x y) :=
  (C.hostCircleMap_injective H).comp (diskArch_injective x y hxy)

theorem hostDiskArc_inside {x y : ℝ} (hxy : x≠y) (t : I) (ht : Inside t) :
    rayLength (C.hostDiskArc H x y t-d.drawing.point v)<C.radius := by
  change rayLength (C.hostCircleMap H (diskArch x y t)-d.drawing.point v)<_
  rw [C.hostCircleMap_rayLength]
  have hnorm : rayLength (diskArch x y t)<1 := by
    unfold rayLength
    exact (Real.sqrt_lt (by positivity) (by norm_num)).mpr (by simpa using diskArch_inside x y hxy t ht)
  simpa using mul_lt_mul_of_pos_left hnorm C.radius_pos

theorem hostDiskArc_radius_le {x y : ℝ} (hxy : x≠y) (t : I) :
    rayLength (C.hostDiskArc H x y t-d.drawing.point v)≤C.radius := by
  by_cases ht0 : t=0
  · subst t
    rw [C.hostDiskArc_zero,C.hostCircleMap_circle H (diskMap_boundary_rayLength x)]
  by_cases ht1 : t=1
  · subst t
    rw [C.hostDiskArc_one,C.hostCircleMap_circle H (diskMap_boundary_rayLength y)]
  exact (C.hostDiskArc_inside H hxy t (PlaneDrawing.inside_of_ne_endpoints ht0 ht1)).le

theorem hostDiskArc_outside_other {x y : ℝ} (hxy : x≠y) (t : I) (w : V) (hvw : v≠w) :
    C.radius<rayLength (C.hostDiskArc H x y t-d.drawing.point w) := by
  apply lt_of_not_ge
  intro hh
  exact Set.disjoint_left.mp (C.disks_disjoint v w hvw) (C.hostDiskArc_radius_le H hxy t) hh

theorem hostDiskArc_interior_notMem_band {x y : ℝ} (hxy : x≠y) (t : I) (ht : Inside t) (e : E) :
    C.hostDiskArc H x y t∉Set.range (C.band Function.injective_id e) := by
  rintro ⟨p,hp⟩
  have hh := C.hostDiskArc_inside H hxy t ht
  rw [← hp] at hh
  exact (not_lt_of_ge (C.band_radius_le Function.injective_id e p v)) hh

theorem hostDiskArcs_disjoint {x y z w : ℝ} (hxy : x≠y) (hzw : z≠w)
    (horder : Noninterleaving (min x y) (max x y) (min z w) (max z w)) :
    Disjoint (Set.range (C.hostDiskArc H x y)) (Set.range (C.hostDiskArc H z w)) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨s,hs⟩ ⟨t,ht⟩
  have he := C.hostCircleMap_injective H (hs.trans ht.symm)
  exact Set.disjoint_left.mp (diskArch_disjoint x y z w hxy hzw horder) ⟨s,rfl⟩ ⟨t,he.symm⟩

theorem height_outside_parent {a p : HostDart G v} (hap : a≠p) (s : I) :
    H.height a s<H.lower p ∨ H.upper p<H.height a s := by
  have hs : H.height a s∈Icc (H.lower a) (H.upper a) := by
    rw [← H.height_range]
    exact ⟨s,rfl⟩
  rcases H.intervals_ordered hap with hh | hh
  · exact Or.inl (hs.2.trans_lt hh)
  · exact Or.inr (hh.trans_le hs.1)

/-- Actual local lane from the i-th sampled input port to the i-th reversed
slot strictly inside the parent fan. Empty families need no exceptional case. -/
def rootwardDiskLane (p : HostDart G v) (n : ℕ) (input : Fin n → HostDart G v × I)
    (i : Fin n) : C(I,Plane) :=
  C.hostDiskArc H (H.height (input i).1 (input i).2) (reversedSlot (H.lower p) (H.upper p) n i)

@[simp] theorem rootwardDiskLane_zero (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (i : Fin n) :
    C.rootwardDiskLane H p n input i 0=C.port (input i).1.val (input i).2 := by
  exact (C.hostDiskArc_zero H _ _).trans (C.hostCircleMap_port H _ _)

@[simp] theorem rootwardDiskLane_one (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (i : Fin n) :
    C.rootwardDiskLane H p n input i 1=C.port p.val (H.slotParameter p n i) := by
  rw [rootwardDiskLane,C.hostDiskArc_one,← H.height_slotParameter p n i,C.hostCircleMap_port]

theorem rootwardDiskLane_injective (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1≠p) (i : Fin n) :
    Function.Injective (C.rootwardDiskLane H p n input i) :=
  C.hostDiskArc_injective H (outside_ne_reversedSlot (H.lower_lt_upper p) n i
    (height_outside_parent H (hout i) _))

theorem rootwardDiskLanes_disjoint (p : HostDart G v) (n : ℕ)
    (input : Fin n → HostDart G v × I) (hout : ∀ i, (input i).1≠p)
    (horder : ∀ i j, i<j → AfterGapOrder (H.lower p) (H.upper p)
      (H.height (input i).1 (input i).2) (H.height (input j).1 (input j).2))
    (i j : Fin n) (hne : i≠j) :
    Disjoint (Set.range (C.rootwardDiskLane H p n input i))
      (Set.range (C.rootwardDiskLane H p n input j)) :=
  C.hostDiskArcs_disjoint H
    (outside_ne_reversedSlot (H.lower_lt_upper p) n i (height_outside_parent H (hout i) _))
    (outside_ne_reversedSlot (H.lower_lt_upper p) n j (height_outside_parent H (hout j) _))
    (reversed_slot_family_noninterleaving (H.lower_lt_upper p) n _ horder i j hne)

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
