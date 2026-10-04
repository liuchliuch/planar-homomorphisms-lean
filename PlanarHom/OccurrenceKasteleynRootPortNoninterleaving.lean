import PlanarHom.OccurrenceKasteleynRootRoutingConstruction
import PlanarHom.PlanarityCircleCrossing

/-! NEW geometric nonalternation of all transported return pairs. This applies
the proved circle crossing theorem to the actual exterior paths, after the
explicit orientation-preserving rotation of the root chart. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.CirclePoleChart
open MultiGraph RadialPottsAssemblyGeometry

theorem rotate_smul (p q : Plane) (r : ℝ) : rotate p (r • q)=r • rotate p q := by
  apply Prod.ext <;> dsimp [rotate] <;> ring

theorem rotate_rayLength {p : Plane} (hp : rayLength p=1) (q : Plane) :
    rayLength (rotate p q)=rayLength q := by
  have hh := unrotate_rayLength hp (rotate p q)
  rw [unrotate_rotate hp] at hh
  exact hh.symm

end PlanarHom.CirclePoleChart

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I))

def orientHost (_C : CircleClipping F (ContinuousMap.id I)) {v : V} (H : HostFanChart F v) : C(Plane,Plane) where
  toFun z := d.drawing.point v+CirclePoleChart.rotate H.pole (z-d.drawing.point v)
  continuous_toFun := by unfold CirclePoleChart.rotate; fun_prop

theorem orientHost_injective {v : V} (H : HostFanChart F v) : Function.Injective (C.orientHost H) := by
  intro x y h
  exact sub_left_inj.mp (CirclePoleChart.rotate_injective H.pole_circle (add_left_cancel h))

theorem orientHost_port {v : V} (H : HostFanChart F v) (a : HostDart G v) (s : I) :
    C.orientHost H (C.port a.val s)=d.drawing.point v+C.radius • diskMap (0,H.height a s) := by
  rw [← C.hostCircleMap_port H a s]
  change d.drawing.point v+CirclePoleChart.rotate H.pole
    ((d.drawing.point v+C.radius • CirclePoleChart.unrotate H.pole (diskMap (0,H.height a s)))-d.drawing.point v)=_
  rw [add_sub_cancel_left,CirclePoleChart.rotate_smul,CirclePoleChart.rotate_unrotate H.pole_circle]

theorem orientHost_radius {v : V} (H : HostFanChart F v) (z : Plane) :
    rayLength (C.orientHost H z-d.drawing.point v)=rayLength (z-d.drawing.point v) := by
  change rayLength ((d.drawing.point v+CirclePoleChart.rotate H.pole (z-d.drawing.point v))-d.drawing.point v)=_
  rw [add_sub_cancel_left,CirclePoleChart.rotate_rayLength H.pole_circle]

theorem no_alternating_host_paths {v : V} (H : HostFanChart F v) (α β : C(I,Plane))
    (a b c e : HostDart G v × I)
    (ha : α 0=C.port a.1.val a.2) (hc : α 1=C.port c.1.val c.2)
    (hb : β 0=C.port b.1.val b.2) (he : β 1=C.port e.1.val e.2)
    (hα : ∀ t, Inside t → C.radius<rayLength (α t-d.drawing.point v))
    (hβ : ∀ t, Inside t → C.radius<rayLength (β t-d.drawing.point v))
    (hdisj : Disjoint (Set.range α) (Set.range β))
    (hab : H.height a.1 a.2<H.height b.1 b.2)
    (hbc : H.height b.1 b.2<H.height c.1 c.2)
    (hce : H.height c.1 c.2<H.height e.1 e.2) : False := by
  let A := (C.orientHost H).comp α
  let B := (C.orientHost H).comp β
  obtain ⟨s,t,hst⟩ := PlanarityCircleCrossing.alternating_scaledCircle_paths_intersect A B
    (d.drawing.point v) C.radius C.radius_pos hab hbc hce
    (by change C.orientHost H (α 0)=_; rw [ha,C.orientHost_port])
    (by change C.orientHost H (α 1)=_; rw [hc,C.orientHost_port])
    (by change C.orientHost H (β 0)=_; rw [hb,C.orientHost_port])
    (by change C.orientHost H (β 1)=_; rw [he,C.orientHost_port])
    (fun t ht => by change C.radius<rayLength (C.orientHost H (α t)-_); rw [C.orientHost_radius]; exact hα t ht)
    (fun t ht => by change C.radius<rayLength (C.orientHost H (β t)-_); rw [C.orientHost_radius]; exact hβ t ht)
  exact Set.disjoint_left.mp hdisj ⟨s,rfl⟩ ⟨t,(C.orientHost_injective H hst).symm⟩

variable (charts : ∀ v, HostFanChart F v)
variable {tree : RootedOccurrenceTree V E} (R : C.RootRouting charts tree)

/-- The paired exterior path in either original occurrence direction. -/
def pairedReturnPath (a : Dart E) (x y : C.PortArrival tree.root)
    (hx : x.label=a) (hy : y.label=(a.1,!a.2)) :
    Path (C.port x.dart.val x.parameter) (C.port y.dart.val y.parameter) := by
  rcases a with ⟨e,b⟩
  cases b
  · exact (C.returnPath e y x hy hx).symm
  · exact C.returnPath e x y hx hy

theorem pairedReturnPath_outside (a : Dart E) (x y : C.PortArrival tree.root)
    (hx : x∈R.outputs) (hy : y∈R.outputs) (hxl : x.label=a) (hyl : y.label=(a.1,!a.2))
    (t : I) (ht : Inside t) :
    C.radius<rayLength (C.pairedReturnPath a x y hxl hyl t-d.drawing.point tree.root) := by
  rcases a with ⟨e,b⟩
  cases b
  · apply C.returnPath_interior_outside charts R e y x hy hx hyl hxl (unitInterval.symm t)
    constructor <;> change _<_ <;> simp only [unitInterval.coe_symm_eq] <;> linarith [ht.1,ht.2]
  · exact C.returnPath_interior_outside charts R e x y hx hy hxl hyl t ht

theorem pairedReturnPaths_disjoint (a b : Dart E) (hab : a.1≠b.1)
    (x y u w : C.PortArrival tree.root) (hx : x∈R.outputs) (hy : y∈R.outputs)
    (hu : u∈R.outputs) (hw : w∈R.outputs)
    (hxl : x.label=a) (hyl : y.label=(a.1,!a.2))
    (hul : u.label=b) (hwl : w.label=(b.1,!b.2)) :
    Disjoint (Set.range (C.pairedReturnPath a x y hxl hyl)) (Set.range (C.pairedReturnPath b u w hul hwl)) := by
  rcases a with ⟨e,be⟩
  rcases b with ⟨f,bf⟩
  cases be <;> cases bf
  all_goals simp only [pairedReturnPath,Path.symm_range]
  · exact C.returnPaths_disjoint charts R e f hab y x w u hy hx hw hu hyl hxl hwl hul
  · exact C.returnPaths_disjoint charts R e f hab y x u w hy hx hu hw hyl hxl hul hwl
  · exact C.returnPaths_disjoint charts R e f hab x y w u hx hy hw hu hxl hyl hwl hul
  · exact C.returnPaths_disjoint charts R e f hab x y u w hx hy hu hw hxl hyl hul hwl

/-- Actual paired root ports cannot alternate in their geometric height order.
Both orientations and original loops are included. -/
theorem no_alternating_root_returns (a b : Dart E) (hab : a.1≠b.1)
    (x y u w : C.PortArrival tree.root) (hx : x∈R.outputs) (hy : y∈R.outputs)
    (hu : u∈R.outputs) (hw : w∈R.outputs)
    (hxl : x.label=a) (hyl : y.label=(a.1,!a.2))
    (hul : u.label=b) (hwl : w.label=(b.1,!b.2)) :
    ¬ ((charts tree.root).height x.dart x.parameter<(charts tree.root).height u.dart u.parameter ∧
      (charts tree.root).height u.dart u.parameter<(charts tree.root).height y.dart y.parameter ∧
      (charts tree.root).height y.dart y.parameter<(charts tree.root).height w.dart w.parameter) := by
  rintro ⟨hxu,huy,hyw⟩
  exact C.no_alternating_host_paths (charts tree.root)
    (C.pairedReturnPath a x y hxl hyl).toContinuousMap (C.pairedReturnPath b u w hul hwl).toContinuousMap
    (x.dart,x.parameter) (u.dart,u.parameter) (y.dart,y.parameter) (w.dart,w.parameter)
    (Path.source _) (Path.target _) (Path.source _) (Path.target _)
    (C.pairedReturnPath_outside charts R a x y hx hy hxl hyl)
    (C.pairedReturnPath_outside charts R b u w hu hw hul hwl)
    (C.pairedReturnPaths_disjoint charts R a b hab x y u w hx hy hu hw hxl hyl hul hwl)
    hxu huy hyw

namespace RootRouting
variable {C charts R}

theorem labelWord_nodup : (R.outputs.map PortArrival.label).Nodup := by
  apply List.pairwise_map.mpr
  apply R.separated.imp_of_mem
  intro x y hx hy hdisj hlabel
  exact Set.disjoint_left.mp hdisj x.source_mem_trace (hlabel.symm ▸ y.source_mem_trace)

/-- Exact sequence-level nonalternation. This is the endpoint consumed by the
discrete contour/fork argument; it refers to the original retained dart labels. -/
theorem no_alternating_label_sublist (a b : Dart E) (hab : a.1≠b.1) :
    ¬ [a,b,(a.1,!a.2),(b.1,!b.2)].Sublist (R.outputs.map PortArrival.label) := by
  intro hs
  obtain ⟨xs,hxs,hm⟩ := List.sublist_map_iff.mp hs
  have hlen : xs.length=4 := by simpa using (congrArg List.length hm).symm
  obtain ⟨x,u,y,w,rfl⟩ := List.length_eq_four.mp hlen
  have hl : x.label=a ∧ u.label=b ∧ y.label=(a.1,!a.2) ∧ w.label=(b.1,!b.2) := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using hm.symm
  have hx : x∈R.outputs := hxs.subset (by simp)
  have hu : u∈R.outputs := hxs.subset (by simp)
  have hy : y∈R.outputs := hxs.subset (by simp)
  have hw : w∈R.outputs := hxs.subset (by simp)
  have hord := R.ordered.sublist hxs
  have hxu := (List.pairwise_cons.mp hord).1 u (by simp)
  have huy := (List.pairwise_cons.mp (List.pairwise_cons.mp hord).2).1 y (by simp)
  have hyw := (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hord).2).2).1 w (by simp)
  exact C.no_alternating_root_returns charts R a b hab x y u w hx hy hu hw
    hl.1 hl.2.2.1 hl.2.1 hl.2.2.2 ⟨hxu,huy,hyw⟩

end RootRouting

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
