import PlanarHom.OccurrenceKasteleynPortArrivals

/-! NEW constructive node operation for the recursive tree routing theorem.
Its hypotheses are exactly the already routed children and local singleton
ports; its result is the explicit whole-path output block for the parent. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) {v : V} (H : HostFanChart F v)

structure LocalArrivals (p : HostDart G v) (block : HostDart G v → List (C.PortArrival v)) : Prop where
  nonloop : G.src p.val.1≠G.dst p.val.1
  placed : ∀ a x, x∈block a → x.dart=a
  ordered : ∀ a, (block a).Pairwise (fun x y => H.height a x.parameter<H.height a y.parameter)
  simple : ∀ a x, x∈block a → x.Simple
  separated : ∀ a b x y, x∈block a → y∈block b → x≠y → Disjoint x.trace y.trace
  contact : ∀ a x, x∈block a → ∀ z∈x.trace, z∈C.hostDisk v → z=C.port x.dart.val x.parameter
  avoid_parent : ∀ a x, x∈block a → Disjoint x.trace (Set.range (C.band Function.injective_id p.val.1))

namespace LocalArrivals
variable {C H} {p : HostDart G v} {block : HostDart G v → List (C.PortArrival v)}
variable (h : C.LocalArrivals H p block)

include h in
theorem input_edge_ne (i : Fin (C.arrivalCount H p block)) :
    (H.rootwardInput p (C.arrivalBlock block) i).1.val.1≠p.val.1 :=
  hostDart_edge_ne_of_ne h.nonloop (H.rootwardInput_ne_parent p (C.arrivalBlock block)
    (C.arrivalBlock_sorted H block h.ordered) i)

theorem incoming_simple (i : Fin (C.arrivalCount H p block)) :
    (C.scannedIncoming H p block h.placed i).Simple := by
  rw [scannedIncoming,IncomingLane.cast_simple]
  obtain ⟨a,ha⟩ := C.scannedArrival_mem H p block i
  exact h.simple a _ ha

theorem incoming_contact (i : Fin (C.arrivalCount H p block)) (z : Plane)
    (hz : z∈(C.scannedIncoming H p block h.placed i).trace) (hd : z∈C.hostDisk v) :
    z=C.port (H.rootwardInput p (C.arrivalBlock block) i).1.val
      (H.rootwardInput p (C.arrivalBlock block) i).2 := by
  rw [C.scannedIncoming_trace] at hz
  obtain ⟨a,ha⟩ := C.scannedArrival_mem H p block i
  rw [C.scannedArrival_input H p block h.placed i]
  exact h.contact a _ ha z hz hd

theorem incoming_avoid_parent (i : Fin (C.arrivalCount H p block)) :
    Disjoint (C.scannedIncoming H p block h.placed i).trace
      (Set.range (C.band Function.injective_id p.val.1)) := by
  rw [C.scannedIncoming_trace]
  obtain ⟨a,ha⟩ := C.scannedArrival_mem H p block i
  exact h.avoid_parent a _ ha

theorem incoming_separated (i j : Fin (C.arrivalCount H p block)) (hne : i≠j) :
    Disjoint (C.scannedIncoming H p block h.placed i).trace
      (C.scannedIncoming H p block h.placed j).trace := by
  rw [C.scannedIncoming_trace,C.scannedIncoming_trace]
  obtain ⟨a,ha⟩ := C.scannedArrival_mem H p block i
  obtain ⟨b,hb⟩ := C.scannedArrival_mem H p block j
  exact h.separated a b _ _ ha hb ((C.scannedArrival_injective H p block h.placed h.ordered).ne hne)

theorem routed_simple {w : V} (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (i : Fin (C.arrivalCount H p block)) :
    (C.routedArrival H p q hq block h.placed i).Simple := by
  change Function.Injective (C.joinedRootward H p _ _ (C.scannedIncoming H p block h.placed) i)
  exact C.joinedRootward_injective H p _ _ _ h.input_edge_ne h.incoming_simple
    h.incoming_contact h.incoming_avoid_parent i

theorem routed_separated {w : V} (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (i j : Fin (C.arrivalCount H p block)) (hne : i≠j) :
    Disjoint (C.routedArrival H p q hq block h.placed i).trace
      (C.routedArrival H p q hq block h.placed j).trace := by
  change Disjoint (Set.range (C.joinedRootward H p _ _ (C.scannedIncoming H p block h.placed) i))
    (Set.range (C.joinedRootward H p _ _ (C.scannedIncoming H p block h.placed) j))
  exact C.joinedRootwards_disjoint H p _ _ _ h.input_edge_ne
    (H.rootwardInput_order p (C.arrivalBlock block) (C.arrivalBlock_sorted H block h.ordered))
    h.incoming_separated h.incoming_contact h.incoming_avoid_parent i j hne

end LocalArrivals

def routedArrivals {w : V} (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (C.PortArrival v)) (h : C.LocalArrivals H p block) : List (C.PortArrival w) :=
  List.ofFn (C.routedArrival H p q hq block h.placed)

theorem routedArrivals_placed {w : V} (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (C.PortArrival v)) (h : C.LocalArrivals H p block)
    (x : C.PortArrival w) (hx : x∈C.routedArrivals H p q hq block h) : x.dart=q := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  rfl

theorem routedArrivals_simple {w : V} (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (C.PortArrival v)) (h : C.LocalArrivals H p block)
    (x : C.PortArrival w) (hx : x∈C.routedArrivals H p q hq block h) : x.Simple := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact h.routed_simple q hq i

theorem routedArrivals_sorted {w : V} (K : HostFanChart F w)
    (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (C.PortArrival v)) (h : C.LocalArrivals H p block) :
    (C.routedArrivals H p q hq block h).Pairwise (fun x y => K.height q x.parameter<K.height q y.parameter) := by
  rw [routedArrivals,List.pairwise_ofFn]
  exact H.opposite_slot_heights_strictMono K p q hq _

theorem routedArrivals_separated {w : V} (p : HostDart G v) (q : HostDart G w) (hq : q.val=(p.val.1,!p.val.2))
    (block : HostDart G v → List (C.PortArrival v)) (h : C.LocalArrivals H p block) :
    (C.routedArrivals H p q hq block h).Pairwise (fun x y => Disjoint x.trace y.trace) := by
  rw [routedArrivals,List.pairwise_ofFn]
  intro i j hij
  exact h.routed_separated q hq i j hij.ne

theorem routedArrivals_contact_other_band {w : V} (p : HostDart G v) (q : HostDart G w)
    (hq : q.val=(p.val.1,!p.val.2)) (block : HostDart G v → List (C.PortArrival v))
    (h : C.LocalArrivals H p block) (e : E) (hep : e≠p.val.1)
    (hold : ∀ a x, x∈block a → ∀ z∈x.trace, z∈Set.range (C.band Function.injective_id e) → z=C.port x.label 0)
    (x : C.PortArrival w) (hx : x∈C.routedArrivals H p q hq block h)
    (z : Plane) (hz : z∈x.trace) (hze : z∈Set.range (C.band Function.injective_id e)) : z=C.port x.label 0 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  rw [C.routedArrival_trace] at hz
  obtain ⟨a,ha⟩ := C.scannedArrival_mem H p block i
  rcases hz with hz | hz
  · exact hold a _ ha z hz hze
  · have he := C.rootwardStep_contact_other_band H p _ _ h.input_edge_ne i e hep z hz hze
    rw [C.scannedArrival_input H p block h.placed i] at he
    have hm : z∈(C.scannedArrival H p block i).trace :=
      he ▸ (C.scannedArrival H p block i).incoming.target_mem_trace
    exact hold a _ ha z hm hze

theorem routedArrivals_support {w : V} (p : HostDart G v) (q : HostDart G w)
    (hq : q.val=(p.val.1,!p.val.2)) (block : HostDart G v → List (C.PortArrival v))
    (h : C.LocalArrivals H p block) (S : Set V) (A : Set E)
    (hold : ∀ a x, x∈block a → x.trace⊆C.clippedRegion S A)
    (x : C.PortArrival w) (hx : x∈C.routedArrivals H p q hq block h) :
    x.trace⊆C.clippedRegion (Set.insert v S) (Set.insert p.val.1 A) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  intro z hz
  rw [C.routedArrival_trace] at hz
  rcases hz with hz | hz
  · obtain ⟨a,ha⟩ := C.scannedArrival_mem H p block i
    rcases hold a _ ha hz with ⟨u,hu,hzu⟩ | ⟨e,he,hze⟩
    · exact Or.inl ⟨u,Set.mem_insert_of_mem _ hu,hzu⟩
    · exact Or.inr ⟨e,Set.mem_insert_of_mem _ he,hze⟩
  · rcases C.rootwardStep_range_subset H p _ _ h.input_edge_ne i hz with hz | hz
    · exact Or.inl ⟨v,Set.mem_insert _ _,hz⟩
    · exact Or.inr ⟨p.val.1,Set.mem_insert _ _,hz⟩

theorem routedArrivals_external_contact {w : V} (p : HostDart G v) (q : HostDart G w)
    (hq : q.val=(p.val.1,!p.val.2)) (block : HostDart G v → List (C.PortArrival v))
    (h : C.LocalArrivals H p block) (u : V) (hvu : v≠u)
    (hold : ∀ a x, x∈block a → Disjoint x.trace (C.hostDisk u))
    (x : C.PortArrival w) (hx : x∈C.routedArrivals H p q hq block h)
    (z : Plane) (hz : z∈x.trace) (hzu : z∈C.hostDisk u) :
    z=C.port x.dart.val x.parameter ∧ w=u := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  have hold' (j : Fin (C.arrivalCount H p block)) :
      Disjoint (C.scannedIncoming H p block h.placed j).trace (C.hostDisk u) := by
    rw [C.scannedIncoming_trace]
    obtain ⟨a,ha⟩ := C.scannedArrival_mem H p block j
    exact hold a _ ha
  have hh := C.joinedRootward_contact_external_disk H p _ _ _ h.input_edge_ne u hvu hold' i z hz hzu
  constructor
  · simpa only [routedArrival,hq] using hh.1
  · exact q.property.symm.trans (by rw [hq]; exact hh.2)

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
