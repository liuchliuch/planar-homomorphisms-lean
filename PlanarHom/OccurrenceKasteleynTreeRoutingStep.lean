import PlanarHom.OccurrenceKasteleynTreeRouting

/-! NEW concrete output and geometric invariants for one complete recursive
occurrence-tree node. All child hypotheses are inherited induction results. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) (charts : ∀ v, HostFanChart F v)
variable {v : V} {children : List (E × RootedOccurrenceTree V E)}
variable (ht : (RootedOccurrenceTree.node v children).Valid G)
variable (routes : ∀ c∈children, C.RoutedBranch charts c.2 c.1)
variable (parent : E) (hdst : G.dst parent=v)
variable (hsrc : G.src parent∉(RootedOccurrenceTree.node v children).vertices)

def nodeOutputs : List (C.PortArrival (G.src parent)) :=
  C.routedArrivals (charts v) ⟨(parent,false),hdst⟩ ⟨(parent,true),rfl⟩ rfl
    (C.nodeArrivalBlock charts ht routes parent) (C.nodeArrivalBlock_local charts ht routes parent hdst hsrc)

theorem nodeOutputs_placed (x : C.PortArrival (G.src parent))
    (hx : x∈C.nodeOutputs charts ht routes parent hdst hsrc) : x.dart.val=(parent,true) :=
  congrArg Subtype.val (C.routedArrivals_placed (charts v) _ _ _ _ _ x hx)

theorem nodeOutputs_simple (x : C.PortArrival (G.src parent))
    (hx : x∈C.nodeOutputs charts ht routes parent hdst hsrc) : x.Simple :=
  C.routedArrivals_simple (charts v) _ _ _ _ _ x hx

theorem nodeOutputs_separated :
    (C.nodeOutputs charts ht routes parent hdst hsrc).Pairwise (fun x y => Disjoint x.trace y.trace) :=
  C.routedArrivals_separated (charts v) _ _ _ _ _

theorem nodeOutputs_ordered :
    (C.nodeOutputs charts ht routes parent hdst hsrc).Pairwise (fun x y =>
      (charts (G.src parent)).height x.dart x.parameter<(charts (G.src parent)).height y.dart y.parameter) := by
  have hsort := C.routedArrivals_sorted (charts v) (charts (G.src parent))
    ⟨(parent,false),hdst⟩ ⟨(parent,true),rfl⟩ rfl
    (C.nodeArrivalBlock charts ht routes parent) (C.nodeArrivalBlock_local charts ht routes parent hdst hsrc)
  apply hsort.imp_of_mem
  intro x y hx hy hh
  have hx' : x.dart=⟨(parent,true),rfl⟩ := Subtype.ext (C.nodeOutputs_placed charts ht routes parent hdst hsrc x hx)
  have hy' : y.dart=⟨(parent,true),rfl⟩ := Subtype.ext (C.nodeOutputs_placed charts ht routes parent hdst hsrc y hy)
  simpa only [hx',hy'] using hh

theorem nodeInput_support (a : HostDart G v) (x : C.PortArrival v)
    (hx : x∈C.nodeArrivalBlock charts ht routes parent a) :
    x.trace⊆C.clippedRegion {u | u∈(RootedOccurrenceTree.node v children).vertices}
      {e | e∈(RootedOccurrenceTree.node v children).edges} := by
  rcases C.nodeArrivalBlock_cases charts ht routes parent a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_,_⟩
  · intro z hz
    rcases C.childArrivals_support charts ht routes c hc x hx hz with ⟨u,hu,hzu⟩ | ⟨e,he,hze⟩
    · refine Or.inl ⟨u,?_,hzu⟩
      rw [vertices_node]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c,hc,hu⟩)
    · refine Or.inr ⟨e,?_,hze⟩
      rw [edges_node]
      exact List.mem_flatMap.mpr ⟨c,hc,he⟩
  · intro z hz
    exact Or.inl ⟨v,(RootedOccurrenceTree.node v children).root_mem_vertices,
      (Set.mem_singleton_iff.mp hz) ▸ C.port_mem_hostDisk a 0⟩

theorem nodeOutputs_support (x : C.PortArrival (G.src parent))
    (hx : x∈C.nodeOutputs charts ht routes parent hdst hsrc) :
    x.trace⊆C.branchRegion (parent,RootedOccurrenceTree.node v children) := by
  have hh := C.routedArrivals_support (charts v) ⟨(parent,false),hdst⟩ ⟨(parent,true),rfl⟩ rfl
    (C.nodeArrivalBlock charts ht routes parent) (C.nodeArrivalBlock_local charts ht routes parent hdst hsrc)
    {u | u∈(RootedOccurrenceTree.node v children).vertices} {e | e∈(RootedOccurrenceTree.node v children).edges}
    (C.nodeInput_support charts ht routes parent) x hx
  intro z hz
  rcases hh hz with ⟨u,hu,hzu⟩ | ⟨e,he,hze⟩
  · refine Or.inl ⟨u,?_,hzu⟩
    rcases hu with hu | hu
    · exact hu.symm ▸ (RootedOccurrenceTree.node v children).root_mem_vertices
    · exact hu
  · exact Or.inr ⟨e,List.mem_cons.mpr he,hze⟩

theorem nodeInput_avoid_external_disk (u : V) (hu : u∉(RootedOccurrenceTree.node v children).vertices)
    (a : HostDart G v) (x : C.PortArrival v) (hx : x∈C.nodeArrivalBlock charts ht routes parent a) :
    Disjoint x.trace (C.hostDisk u) := by
  rcases C.nodeArrivalBlock_cases charts ht routes parent a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_,_⟩
  · exact (C.branchRegion_disjoint_external_disk ht c hc u hu).mono_left (C.childArrivals_support charts ht routes c hc x hx)
  · apply Set.disjoint_left.mpr
    intro z hz hzu
    exact Set.disjoint_left.mp (C.disks_disjoint v u (fun he => hu (he ▸ (RootedOccurrenceTree.node v children).root_mem_vertices)))
      ((Set.mem_singleton_iff.mp hz) ▸ C.port_mem_hostDisk a 0) hzu

theorem nodeOutputs_contact_disk (x : C.PortArrival (G.src parent))
    (hx : x∈C.nodeOutputs charts ht routes parent hdst hsrc)
    (u : V) (hu : u∉(RootedOccurrenceTree.node v children).vertices)
    (z : Plane) (hz : z∈x.trace) (hzu : z∈C.hostDisk u) :
    z=C.port x.dart.val x.parameter ∧ G.src parent=u :=
  C.routedArrivals_external_contact (charts v) _ _ _ _ _ u
    (fun he => hu (he ▸ (RootedOccurrenceTree.node v children).root_mem_vertices))
    (C.nodeInput_avoid_external_disk charts ht routes parent u hu) x hx z hz hzu

theorem nodeInput_contact_band (e : E) (he : e∉parent::(RootedOccurrenceTree.node v children).edges)
    (a : HostDart G v) (x : C.PortArrival v) (hx : x∈C.nodeArrivalBlock charts ht routes parent a)
    (z : Plane) (hz : z∈x.trace) (hze : z∈Set.range (C.band Function.injective_id e)) : z=C.port x.label 0 := by
  rcases C.nodeArrivalBlock_cases charts ht routes parent a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_,_⟩
  · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    simp only [PortArrival.castHost_trace,PortArrival.castHost_label] at *
    apply (routes c hc).contact_band y hy e _ z hz hze
    intro hem
    apply he
    apply List.mem_cons_of_mem
    rw [edges_node]
    exact List.mem_flatMap.mpr ⟨c,hc,hem⟩
  · exact Set.mem_singleton_iff.mp hz

theorem nodeOutputs_contact_band (x : C.PortArrival (G.src parent))
    (hx : x∈C.nodeOutputs charts ht routes parent hdst hsrc)
    (e : E) (he : e∉parent::(RootedOccurrenceTree.node v children).edges)
    (z : Plane) (hz : z∈x.trace) (hze : z∈Set.range (C.band Function.injective_id e)) : z=C.port x.label 0 :=
  C.routedArrivals_contact_other_band (charts v) _ _ _ _ _ e
    (fun hh => he (List.mem_cons.mpr (Or.inl hh)))
    (C.nodeInput_contact_band charts ht routes parent e he) x hx z hz hze

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
