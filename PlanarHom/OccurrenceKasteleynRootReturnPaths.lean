import PlanarHom.OccurrenceKasteleynRootRouting
import PlanarHom.IncomingLaneConnection

/-! NEW actual return arcs exterior to the root circle. Every original
non-tree band is connected to its two transported ports by the constructed
rootward lanes; simplicity, mutual separation, and strict exterior interior
are consequences of the exact contact invariants. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) (charts : ∀ v, HostFanChart F v)
variable {tree : RootedOccurrenceTree V E} (R : C.RootRouting charts tree)

theorem port_on_host_circle {v : V} (a : HostDart G v) (s : I) :
    rayLength (C.port a.val s-d.drawing.point v)=C.radius := by
  rw [C.port_formula,a.property,add_sub_cancel_left,rayLength_smul,abs_of_pos C.radius_pos,
    normalizedFan_circle,mul_one]

namespace RootRouting
variable {C charts R}

theorem separated_of_labels_ne {x y : C.PortArrival tree.root} (hx : x∈R.outputs) (hy : y∈R.outputs)
    (hne : x.label≠y.label) : Disjoint x.trace y.trace :=
  R.separated.forall (fun _ _ h => h.symm) hx hy (fun h => hne (congrArg PortArrival.label h))

theorem output_edge_not_tree {x : C.PortArrival tree.root} (hx : x∈R.outputs) : x.label.1∉tree.edges :=
  ((R.labels x.label).mp (List.mem_map.mpr ⟨x,hx,rfl⟩)).2

theorem trace_radius_le {x : C.PortArrival tree.root} (hx : x∈R.outputs) (z : Plane) (hz : z∈x.trace) :
    C.radius≤rayLength (z-d.drawing.point tree.root) := by
  by_contra hh
  have hlt := lt_of_not_ge hh
  have he := R.contact_root x hx z hz hlt.le
  rw [he,C.port_on_host_circle] at hlt
  exact (lt_irrefl _ hlt)

end RootRouting

def returnMiddle (e : E) (x y : C.PortArrival tree.root) (hx : x.label=(e,true)) (hy : y.label=(e,false)) :
    Path x.incoming.source y.incoming.source :=
  (C.bandLanePath (e,true) 0).cast
    (x.source_eq.trans (congrArg (fun a => C.port a 0) hx))
    (y.source_eq.trans (congrArg (fun a => C.port a 0) hy))

def returnPath (e : E) (x y : C.PortArrival tree.root) (hx : x.label=(e,true)) (hy : y.label=(e,false)) :
    Path (C.port x.dart.val x.parameter) (C.port y.dart.val y.parameter) :=
  x.incoming.connect y.incoming (C.returnMiddle e x y hx hy)

theorem returnPath_range (e : E) (x y : C.PortArrival tree.root) (hx : x.label=(e,true)) (hy : y.label=(e,false)) :
    Set.range (C.returnPath e x y hx hy)=x.trace ∪ (Set.range (C.bandLane (e,true) 0) ∪ y.trace) :=
  x.incoming.connect_range y.incoming _

theorem returnPath_injective (e : E) (x y : C.PortArrival tree.root)
    (hx : x∈R.outputs) (hy : y∈R.outputs) (hxl : x.label=(e,true)) (hyl : y.label=(e,false)) :
    Function.Injective (C.returnPath e x y hxl hyl) := by
  have he : e∉tree.edges := by simpa only [hxl] using R.output_edge_not_tree hx
  apply x.incoming.connect_injective y.incoming _ (R.simple x hx) (R.simple y hy)
    (C.bandLane_injective (e,true) 0)
  · exact R.separated_of_labels_ne hx hy (by rw [hxl,hyl]; simp)
  · intro z hzx hzm
    obtain ⟨t,ht⟩ := hzm
    have hb : z∈Set.range (C.band Function.injective_id e) := ht ▸ C.bandLane_mem_band (e,true) 0 t
    exact (R.contact_band x hx e he z hzx hb).trans x.source_eq.symm
  · intro z hzm hzy
    obtain ⟨t,ht⟩ := hzm
    have hb : z∈Set.range (C.band Function.injective_id e) := ht ▸ C.bandLane_mem_band (e,true) 0 t
    exact (R.contact_band y hy e he z hzy hb).trans y.source_eq.symm

theorem returnPath_radius_le (e : E) (x y : C.PortArrival tree.root)
    (hx : x∈R.outputs) (hy : y∈R.outputs) (hxl : x.label=(e,true)) (hyl : y.label=(e,false)) (t : I) :
    C.radius≤rayLength (C.returnPath e x y hxl hyl t-d.drawing.point tree.root) := by
  have hm : C.returnPath e x y hxl hyl t∈Set.range (C.returnPath e x y hxl hyl) := ⟨t,rfl⟩
  rw [C.returnPath_range] at hm
  rcases hm with hm | ⟨s,hs⟩ | hm
  · exact R.trace_radius_le hx _ hm
  · rw [← hs]
    exact C.band_radius_le Function.injective_id e (s,0) tree.root
  · exact R.trace_radius_le hy _ hm

theorem returnPath_circle_contact (e : E) (x y : C.PortArrival tree.root)
    (hx : x∈R.outputs) (hy : y∈R.outputs) (hxl : x.label=(e,true)) (hyl : y.label=(e,false))
    (z : Plane) (hz : z∈Set.range (C.returnPath e x y hxl hyl)) (hd : z∈C.hostDisk tree.root) :
    z=C.port x.dart.val x.parameter ∨ z=C.port y.dart.val y.parameter := by
  rw [C.returnPath_range] at hz
  rcases hz with hz | ⟨s,hs⟩ | hz
  · exact Or.inl (R.contact_root x hx z hz hd)
  · have hc : rayLength (C.band Function.injective_id e (s,0)-d.drawing.point tree.root)=C.radius :=
      le_antisymm (hs.symm ▸ hd) (C.band_radius_le Function.injective_id e (s,0) tree.root)
    rcases (C.band_on_circle_iff Function.injective_id e (s,0) tree.root).mp hc with ⟨hs0,_⟩ | ⟨hs1,_⟩
    · change s=0 at hs0
      have hz' : z=C.port x.label 0 := by
        rw [← hs,hs0,C.bandLane_zero,hxl]
      exact Or.inl (R.contact_root x hx z (hz' ▸ x.source_mem_trace) hd)
    · change s=1 at hs1
      have hz' : z=C.port y.label 0 := by
        rw [← hs,hs1,C.bandLane_one,hyl]
        rfl
      exact Or.inr (R.contact_root y hy z (hz' ▸ y.source_mem_trace) hd)
  · exact Or.inr (R.contact_root y hy z hz hd)

theorem returnPath_interior_outside (e : E) (x y : C.PortArrival tree.root)
    (hx : x∈R.outputs) (hy : y∈R.outputs) (hxl : x.label=(e,true)) (hyl : y.label=(e,false))
    (t : I) (ht : Inside t) :
    C.radius<rayLength (C.returnPath e x y hxl hyl t-d.drawing.point tree.root) := by
  apply lt_of_not_ge
  intro hd
  rcases C.returnPath_circle_contact charts R e x y hx hy hxl hyl _ ⟨t,rfl⟩ hd with hh | hh
  · have he : t=0 := C.returnPath_injective charts R e x y hx hy hxl hyl (hh.trans (Path.source _).symm)
    subst t
    exact (lt_irrefl (0:ℝ) ht.1)
  · have he : t=1 := C.returnPath_injective charts R e x y hx hy hxl hyl (hh.trans (Path.target _).symm)
    subst t
    exact (lt_irrefl (1:ℝ) ht.2)

theorem outputTrace_disjoint_other_middle (x : C.PortArrival tree.root) (hx : x∈R.outputs)
    (e : E) (he : e∉tree.edges) (hne : x.label.1≠e) :
    Disjoint x.trace (Set.range (C.bandLane (e,true) 0)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨t,ht⟩
  have hb : z∈Set.range (C.band Function.injective_id e) := ht ▸ C.bandLane_mem_band (e,true) 0 t
  have hh := R.contact_band x hx e he z hz hb
  exact C.port_notMem_other_band hne 0 (hh ▸ hb)

theorem returnPaths_disjoint (e f : E) (hef : e≠f)
    (x y u w : C.PortArrival tree.root) (hx : x∈R.outputs) (hy : y∈R.outputs)
    (hu : u∈R.outputs) (hw : w∈R.outputs)
    (hxl : x.label=(e,true)) (hyl : y.label=(e,false))
    (hul : u.label=(f,true)) (hwl : w.label=(f,false)) :
    Disjoint (Set.range (C.returnPath e x y hxl hyl)) (Set.range (C.returnPath f u w hul hwl)) := by
  have he : e∉tree.edges := by simpa only [hxl] using R.output_edge_not_tree hx
  have hf : f∉tree.edges := by simpa only [hul] using R.output_edge_not_tree hu
  have hxu := R.separated_of_labels_ne hx hu (by intro h; exact hef (by simpa only [hxl,hul] using congrArg Prod.fst h))
  have hxw := R.separated_of_labels_ne hx hw (by intro h; exact hef (by simpa only [hxl,hwl] using congrArg Prod.fst h))
  have hyu := R.separated_of_labels_ne hy hu (by intro h; exact hef (by simpa only [hyl,hul] using congrArg Prod.fst h))
  have hyw := R.separated_of_labels_ne hy hw (by intro h; exact hef (by simpa only [hyl,hwl] using congrArg Prod.fst h))
  have hxf := C.outputTrace_disjoint_other_middle charts R x hx f hf (by simpa only [hxl] using hef)
  have hyf := C.outputTrace_disjoint_other_middle charts R y hy f hf (by simpa only [hyl] using hef)
  have hue := C.outputTrace_disjoint_other_middle charts R u hu e he (by simpa only [hul] using hef.symm)
  have hwe := C.outputTrace_disjoint_other_middle charts R w hw e he (by simpa only [hwl] using hef.symm)
  have hmid := C.bandLanes_disjoint (a:=(e,true)) (b:=(f,true)) (s:=0) (t:=0) (Or.inl hef)
  rw [C.returnPath_range,C.returnPath_range]
  exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hxu,disjoint_union_right.mpr ⟨hxf,hxw⟩⟩,
    disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hue.symm,disjoint_union_right.mpr ⟨hmid,hwe.symm⟩⟩,
      disjoint_union_right.mpr ⟨hyu,disjoint_union_right.mpr ⟨hyf,hyw⟩⟩⟩⟩

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
