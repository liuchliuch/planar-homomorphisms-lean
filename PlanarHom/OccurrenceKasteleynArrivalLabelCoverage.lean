import PlanarHom.OccurrenceKasteleynRouteArrivalBlocks

/-! NEW exact label word and coverage of the actual finite arrival router. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.PlanarityLRRealization

theorem mem_afterParentInputs_of_empty {A B : Type*} [DecidableEq A]
    (row : List A) (parent : A) (block : A → List B) (hp : parent∈row)
    (hempty : block parent=[]) (x : B) :
    x∈afterParentInputs row parent block ↔ x∈row.flatMap block := by
  have hidx := List.idxOf_lt_length_iff.mpr hp
  have hs := List.take_append_drop (row.idxOf parent) row
  rw [List.drop_eq_getElem_cons hidx,List.getElem_idxOf hidx] at hs
  conv_rhs => rw [← hs]
  simp only [afterParentInputs,List.flatMap_append,List.flatMap_cons,hempty,List.nil_append,
    List.mem_append]
  exact or_comm

end PlanarHom.PlanarityLRRealization
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
local instance arrivalCoverageEq : DecidableEq E := Classical.decEq E
variable (C : CircleClipping F (ContinuousMap.id I)) {v : V} (H : HostFanChart F v)

theorem routedArrivals_label_word {w : V} (p : HostDart G v) (q : HostDart G w)
    (hq : q.val=(p.val.1,!p.val.2)) (block : HostDart G v → List (C.PortArrival v))
    (h : C.LocalArrivals H p block) :
    (C.routedArrivals H p q hq block h).map PortArrival.label =
      afterParentInputs H.row p (fun a => (block a).map PortArrival.label) := by
  classical
  have he : (C.routedArrivals H p q hq block h).map PortArrival.label =
      (H.rootwardInputWord p (C.arrivalBlock block)).map (fun x => x.1.label) := by
    rw [routedArrivals,List.map_ofFn,← List.ofFn_get (H.rootwardInputWord p (C.arrivalBlock block)),List.map_ofFn]
    rfl
  rw [he]
  simp only [HostFanChart.rootwardInputWord,arrivalBlock,afterParentInputs,List.map_append,
    List.map_flatMap,List.map_map,Function.comp_def]

theorem mem_routedArrivals_labels {w : V} (p : HostDart G v) (q : HostDart G w)
    (hq : q.val=(p.val.1,!p.val.2)) (block : HostDart G v → List (C.PortArrival v))
    (h : C.LocalArrivals H p block) (hempty : block p=[]) (a : Dart E) :
    a∈(C.routedArrivals H p q hq block h).map PortArrival.label ↔
      ∃ b : HostDart G v, ∃ x∈block b, x.label=a := by
  classical
  rw [C.routedArrivals_label_word H p q hq block h,
    mem_afterParentInputs_of_empty H.row p _ (H.mem_row p) (by rw [hempty]; rfl)]
  simp only [List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨b,_,x,hx,he⟩
    exact ⟨b,x,hx,he⟩
  · rintro ⟨b,x,hx,he⟩
    exact ⟨b,H.mem_row b,x,hx,he⟩

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
