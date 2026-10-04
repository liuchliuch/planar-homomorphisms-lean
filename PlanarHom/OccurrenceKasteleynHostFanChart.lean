import PlanarHom.OccurrenceKasteleynCircleFans
import PlanarHom.CirclePoleChart
import PlanarHom.OccurrenceKasteleynCircleClippingBridge

/-! NEW local geometric contour intervals. The actual fan gap and explicit
orientation-preserving Cayley chart turn each host's disjoint closed fans into
disjoint real intervals. No rotation/gap/order certificate is assumed. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData
open Kasteleyn RadialPottsAssemblyGeometry
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} (F : ∀ a, D.EndpointFan positive a (rays a))

abbrev HostDart (G : MultiGraph V E) (v : V) := {a : Dart E // (G.dartPair a).1=v}

/-- Constructed geometric chart for every closed fan at one actual host. -/
structure HostFanChart (v : V) where
  pole : Plane
  pole_circle : rayLength pole=1
  gap : ∀ a : HostDart G v, ∀ s : I, normalizedFan F a.val s≠pole
  height : HostDart G v → C(I,ℝ)
  realizes : ∀ a s, diskMap (0,height a s)=CirclePoleChart.rotate pole (normalizedFan F a.val s)
  injective : Function.Injective (fun p : HostDart G v × I => height p.1 p.2)

namespace CircleClipping
variable {F}

/-- No local chart or angular gap is an input: all data are extracted from the
literal recovered clipping and its proved separation. -/
theorem exists_hostFanChart (C : CircleClipping F (ContinuousMap.id I)) (v : V) :
    Nonempty (HostFanChart F v) := by
  obtain ⟨p,hp,hgap⟩ := C.exists_host_fan_gap v
  let curve (a : HostDart G v) : C(I,Plane) :=
    ⟨fun s => normalizedFan F a.val s,(normalizedFan F a.val).continuous.comp continuous_subtype_val⟩
  let H (a : HostDart G v) : C(I,ℝ) := CirclePoleChart.heightPath hp (curve a)
    (fun s => hgap a.val a.property s)
  refine ⟨⟨p,hp,(fun a => hgap a.val a.property),H,?_,?_⟩⟩
  · intro a s
    exact CirclePoleChart.height_realizes hp (normalizedFan_circle F a.val s)
      (hgap a.val a.property s)
  · rintro ⟨a,s⟩ ⟨b,t⟩ heq
    have hfan := CirclePoleChart.height_injective hp (normalizedFan_circle F a.val s)
      (normalizedFan_circle F b.val t) (hgap a.val a.property s) (hgap b.val b.property t) heq
    have hport : C.port a.val s=C.port b.val t := by
      rw [C.port_formula,C.port_formula,a.property,b.property]
      exact congrArg (fun q : Plane => d.drawing.point v+C.radius • q) hfan
    obtain ⟨hab,hst⟩ := C.port_injective hport
    exact Prod.ext (Subtype.ext hab) hst

end CircleClipping

namespace HostFanChart
variable {F} {v : V} (H : HostFanChart F v)

theorem height_injective (a : HostDart G v) : Function.Injective (H.height a) := by
  intro s t h
  have he : (a,s)=(a,t) := H.injective h
  exact congrArg Prod.snd he

theorem height_monotone (a : HostDart G v) : StrictMono (H.height a) ∨ StrictAnti (H.height a) :=
  (H.height a).continuous.strictMono_of_inj_boundedOrder' (H.height_injective a)

def lower (a : HostDart G v) : ℝ := min (H.height a 0) (H.height a 1)
def upper (a : HostDart G v) : ℝ := max (H.height a 0) (H.height a 1)

theorem lower_lt_upper (a : HostDart G v) : H.lower a<H.upper a := by
  have hn : H.height a 0≠H.height a 1 := (H.height_injective a).ne (by norm_num)
  rcases lt_or_gt_of_ne hn with hh | hh
  · simp [lower,upper,min_eq_left hh.le,max_eq_right hh.le,hh]
  · simp [lower,upper,min_eq_right hh.le,max_eq_left hh.le,hh]

/-- The complete closed fan, not merely its endpoints, becomes this exact interval. -/
theorem height_range (a : HostDart G v) : Set.range (H.height a)=Set.Icc (H.lower a) (H.upper a) := by
  ext x
  constructor
  · rintro ⟨s,rfl⟩
    rcases H.height_monotone a with hm | hm
    · have h01 := hm.monotone (show (0:I)≤1 from bot_le)
      simp only [lower,upper,min_eq_left h01,max_eq_right h01,Set.mem_Icc]
      exact ⟨hm.monotone bot_le,hm.monotone le_top⟩
    · have h10 := hm.antitone (show (0:I)≤1 from bot_le)
      simp only [lower,upper,min_eq_right h10,max_eq_left h10,Set.mem_Icc]
      exact ⟨hm.antitone le_top,hm.antitone bot_le⟩
  · intro hx
    by_cases hh : H.height a 0≤H.height a 1
    · simp only [lower,upper,min_eq_left hh,max_eq_right hh] at hx
      obtain ⟨s,_,hs⟩ := (isPreconnected_univ : IsPreconnected (Set.univ : Set I)).intermediate_value
        (a := 0) (b := 1) (Set.mem_univ _) (Set.mem_univ _) (H.height a).continuous.continuousOn hx
      exact ⟨s,hs⟩
    · have hh' := le_of_not_ge hh
      simp only [lower,upper,min_eq_right hh',max_eq_left hh'] at hx
      obtain ⟨s,_,hs⟩ := (isPreconnected_univ : IsPreconnected (Set.univ : Set I)).intermediate_value
        (a := 1) (b := 0) (Set.mem_univ _) (Set.mem_univ _) (H.height a).continuous.continuousOn hx
      exact ⟨s,hs⟩

theorem intervals_disjoint {a b : HostDart G v} (hab : a≠b) :
    Disjoint (Set.Icc (H.lower a) (H.upper a)) (Set.Icc (H.lower b) (H.upper b)) := by
  rw [← H.height_range a,← H.height_range b]
  apply Set.disjoint_left.mpr
  rintro x ⟨s,hs⟩ ⟨t,ht⟩
  have he : (a,s)=(b,t) := H.injective (hs.trans ht.symm)
  exact hab (congrArg Prod.fst he)

/-- Every pair of distinct incident closed fans has a strict, positive chart gap. -/
theorem intervals_ordered {a b : HostDart G v} (hab : a≠b) :
    H.upper a<H.lower b ∨ H.upper b<H.lower a := by
  by_contra hn
  push_neg at hn
  have ha := (H.lower_lt_upper a).le
  have hb := (H.lower_lt_upper b).le
  have hxA : max (H.lower a) (H.lower b)∈Set.Icc (H.lower a) (H.upper a) :=
    ⟨le_max_left _ _,max_le ha hn.1⟩
  have hxB : max (H.lower a) (H.lower b)∈Set.Icc (H.lower b) (H.upper b) :=
    ⟨le_max_right _ _,max_le hn.2 hb⟩
  exact Set.disjoint_left.mp (H.intervals_disjoint hab) hxA hxB

local instance : Fintype (HostDart G v) := Fintype.ofFinite _

/-- Literal geometric cyclic row, cut at the constructed omitted circle point.
Sorting whole closed fan intervals rather than just center rays exposes exact
positive corner gaps. -/
def row : List (HostDart G v) := by
  classical
  exact (Finset.univ.toList).mergeSort (fun a b => decide (H.lower a≤H.lower b))

theorem row_perm : H.row.Perm (Finset.univ.toList : List (HostDart G v)) := by
  classical
  exact List.mergeSort_perm _ _

theorem mem_row (a : HostDart G v) : a∈H.row := by
  classical
  rw [H.row_perm.mem_iff]
  simp

theorem row_nodup : H.row.Nodup := by
  classical
  exact H.row_perm.symm.nodup (Finset.nodup_toList _)

theorem row_sorted_lower : H.row.Pairwise (fun a b => H.lower a≤H.lower b) := by
  classical
  have htrans (a b c : HostDart G v) (hab : decide (H.lower a≤H.lower b)=true)
      (hbc : decide (H.lower b≤H.lower c)=true) : decide (H.lower a≤H.lower c)=true := by
    exact decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc))
  have htotal (a b : HostDart G v) :
      (decide (H.lower a≤H.lower b) || decide (H.lower b≤H.lower a))=true := by
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact le_total _ _
  have hh := List.sorted_mergeSort htrans htotal (Finset.univ.toList : List (HostDart G v))
  apply hh.imp
  intro a b h
  exact of_decide_eq_true h

/-- Any earlier fan lies strictly before the entire later fan. These are the
actual geometric corner gaps needed by tree-collar contour routing. -/
theorem row_strict_gaps : H.row.Pairwise (fun a b => H.upper a<H.lower b) := by
  have hn : H.row.Pairwise (fun a b => a≠b) := H.row_nodup
  apply ((H.row_sorted_lower).and hn).imp
  intro a b hab
  rcases H.intervals_ordered hab.2 with hh | hh
  · exact hh
  · have hsize := H.lower_lt_upper b
    linarith [hab.1]

/-- Erase only the incident-host proof, retaining every literal dart occurrence. -/
def dartRow : List (Dart E) := H.row.map Subtype.val

theorem dartRow_nodup : H.dartRow.Nodup := H.row_nodup.map Subtype.val_injective

theorem mem_dartRow (a : Dart E) : a∈H.dartRow ↔ (G.dartPair a).1=v := by
  constructor
  · intro h
    obtain ⟨b,_,hba⟩ := List.mem_map.mp h
    exact hba ▸ b.property
  · intro ha
    exact List.mem_map.mpr ⟨⟨a,ha⟩,H.mem_row _,rfl⟩

end HostFanChart
end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData

namespace PlanarHom.MultiGraph
open Kasteleyn PolygonalDrawing.TwoSidedStripData
open scoped unitInterval
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

/-- Ordinary finite planarity alone supplies the concrete fans, a common circle
clipping, and all local geometric dart rows with proved positive corner gaps. -/
theorem Planar.exists_circlePortRows (h : G.Planar) (positive : Bool) :
    ∃ d : PolygonalDrawing G, ∃ D : d.refineSingle.TwoSidedStripData,
      ∃ rays : Dart E → Plane, (∀ a, rays a≠0) ∧
      ∃ F : ∀ a, D.EndpointFan positive a (rays a),
      ∃ _C : CircleClipping F (ContinuousMap.id I), Nonempty (∀ v, HostFanChart F v) := by
  classical
  obtain ⟨d,D,rays,hne,F,⟨C⟩⟩ := h.exists_polygonal_circleClipping positive
  exact ⟨d,D,rays,hne,F,C,⟨fun v => Classical.choice (C.exists_hostFanChart v)⟩⟩

end PlanarHom.MultiGraph
