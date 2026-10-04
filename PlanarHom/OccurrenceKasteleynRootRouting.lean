import PlanarHom.OccurrenceKasteleynTreeRoutingStep

/-! NEW final root assembly. Child lanes end on the actual root circle and
local retained ports stay at their original circle point. No root disk arc is
inserted. The output order is the literal flatMap of its geometric cyclic row. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) (charts : ∀ v, HostFanChart F v)

structure RootRouting (tree : RootedOccurrenceTree V E) where
  outputs : List (C.PortArrival tree.root)
  word : RootWord charts tree (outputs.map PortArrival.label)
  ordered : outputs.Pairwise (fun x y =>
    (charts tree.root).height x.dart x.parameter<(charts tree.root).height y.dart y.parameter)
  simple : ∀ x∈outputs, x.Simple
  separated : outputs.Pairwise (fun x y => Disjoint x.trace y.trace)
  support : ∀ x∈outputs, x.trace⊆C.clippedRegion {v | v∈tree.vertices} {e | e∈tree.edges}
  labels : ∀ a, a∈outputs.map PortArrival.label ↔ (G.dartPair a).1∈tree.vertices ∧ a.1∉tree.edges
  contact_root : ∀ x∈outputs, ∀ z∈x.trace, z∈C.hostDisk tree.root → z=C.port x.dart.val x.parameter
  contact_band : ∀ x∈outputs, ∀ e, e∉tree.edges →
    ∀ z∈x.trace, z∈Set.range (C.band Function.injective_id e) → z=C.port x.label 0

variable {v : V} {children : List (E × RootedOccurrenceTree V E)}
variable (ht : (RootedOccurrenceTree.node v children).Valid G)
variable (routes : ∀ c∈children, C.RoutedBranch charts c.2 c.1)

def rootArrivalBlock (a : HostDart G v) : List (C.PortArrival v) := by
  classical
  exact if h : ∃ t, (a.val.1,t)∈children then
    C.childArrivals charts ht routes (a.val.1,Classical.choose h) (Classical.choose_spec h)
  else [PortArrival.localPort a]

def rootOutputs : List (C.PortArrival v) := (charts v).row.flatMap (C.rootArrivalBlock charts ht routes)

theorem rootArrivalBlock_cases (a : HostDart G v) (x : C.PortArrival v)
    (hx : x∈C.rootArrivalBlock charts ht routes a) :
    (∃ c, ∃ hc : c∈children, c.1=a.val.1 ∧ x∈C.childArrivals charts ht routes c hc) ∨
      (x=PortArrival.localPort a ∧ ∀ t, (a.val.1,t)∉children) := by
  classical
  unfold rootArrivalBlock at hx
  split_ifs at hx with hc
  · exact Or.inl ⟨_,Classical.choose_spec hc,rfl,hx⟩
  · exact Or.inr ⟨List.mem_singleton.mp hx,by simpa only [not_exists] using hc⟩

theorem rootArrivalBlock_placed (a : HostDart G v) (x : C.PortArrival v)
    (hx : x∈C.rootArrivalBlock charts ht routes a) : x.dart=a := by
  rcases C.rootArrivalBlock_cases charts ht routes a x hx with ⟨c,hc,he,hx⟩ | ⟨rfl,_⟩
  · exact Subtype.ext ((C.childArrivals_placed charts ht routes c hc x hx).trans (child_dart_eq ht c hc a he).symm)
  · rfl

theorem rootArrivalBlock_ordered (a : HostDart G v) :
    (C.rootArrivalBlock charts ht routes a).Pairwise (fun x y =>
      (charts v).height a x.parameter<(charts v).height a y.parameter) := by
  classical
  unfold rootArrivalBlock
  split_ifs with hc
  · apply (C.childArrivals_ordered charts ht routes _ (Classical.choose_spec hc)).imp_of_mem
    intro x y hx hy hxy
    have ha := child_dart_eq ht (a.val.1,Classical.choose hc) (Classical.choose_spec hc) a rfl
    have hxa : x.dart=a := Subtype.ext ((C.childArrivals_placed charts ht routes _ _ x hx).trans ha.symm)
    have hya : y.dart=a := Subtype.ext ((C.childArrivals_placed charts ht routes _ _ y hy).trans ha.symm)
    simpa only [hxa,hya] using hxy
  · simp

theorem rootArrivalBlock_separated (a b : HostDart G v) (x y : C.PortArrival v)
    (hx : x∈C.rootArrivalBlock charts ht routes a) (hy : y∈C.rootArrivalBlock charts ht routes b)
    (hne : x≠y) : Disjoint x.trace y.trace := by
  rcases C.rootArrivalBlock_cases charts ht routes a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,ha⟩
  · rcases C.rootArrivalBlock_cases charts ht routes b y hy with ⟨k,hk,_,hy⟩ | ⟨rfl,hb⟩
    · by_cases hck : c=k
      · subst k
        exact (C.childArrivals_separated charts ht routes c hc).forall (fun _ _ h => h.symm) hx hy hne
      · exact ((C.branchRegions_disjoint ht).forall (fun _ _ h => h.symm) hc hk hck).mono
          (C.childArrivals_support charts ht routes c hc x hx) (C.childArrivals_support charts ht routes k hk y hy)
    · exact C.child_local_disjoint charts ht routes c hc x hx b hb
  · rcases C.rootArrivalBlock_cases charts ht routes b y hy with ⟨k,hk,_,hy⟩ | ⟨rfl,_⟩
    · exact (C.child_local_disjoint charts ht routes k hk y hy a ha).symm
    · apply Set.disjoint_left.mpr
      intro z hz₁ hz₂
      have he := (Set.mem_singleton_iff.mp hz₁).symm.trans (Set.mem_singleton_iff.mp hz₂)
      exact hne (congrArg PortArrival.localPort (Subtype.ext (C.port_injective he).1))

theorem rootOutputs_simple (x : C.PortArrival v) (hx : x∈C.rootOutputs charts ht routes) : x.Simple := by
  obtain ⟨a,_,hx⟩ := List.mem_flatMap.mp hx
  rcases C.rootArrivalBlock_cases charts ht routes a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_⟩
  · exact C.childArrivals_simple charts ht routes c hc x hx
  · exact PortArrival.localPort_simple a

theorem rootOutputs_ordered : (C.rootOutputs charts ht routes).Pairwise (fun x y =>
    (charts v).height x.dart x.parameter<(charts v).height y.dart y.parameter) := by
  apply flatMap_height_sorted (charts v).row (C.rootArrivalBlock charts ht routes)
    (charts v).lower (charts v).upper (fun x => (charts v).height x.dart x.parameter)
    (charts v).row_strict_gaps
  · intro a
    apply (C.rootArrivalBlock_ordered charts ht routes a).imp_of_mem
    intro x y hx hy hh
    simpa only [C.rootArrivalBlock_placed charts ht routes a x hx,C.rootArrivalBlock_placed charts ht routes a y hy] using hh
  · intro a x hx
    rw [C.rootArrivalBlock_placed charts ht routes a x hx]
    change (charts v).height a x.parameter∈Icc ((charts v).lower a) ((charts v).upper a)
    rw [← HostFanChart.height_range]
    exact ⟨x.parameter,rfl⟩

theorem rootOutputs_separated :
    (C.rootOutputs charts ht routes).Pairwise (fun x y => Disjoint x.trace y.trace) := by
  apply (C.rootOutputs_ordered charts ht routes).imp_of_mem
  intro x y hx hy hxy
  obtain ⟨a,_,hax⟩ := List.mem_flatMap.mp hx
  obtain ⟨b,_,hby⟩ := List.mem_flatMap.mp hy
  exact C.rootArrivalBlock_separated charts ht routes a b x y hax hby (fun he => by rw [he] at hxy; exact (lt_irrefl _ hxy))

theorem rootOutputs_contact_root (x : C.PortArrival v) (hx : x∈C.rootOutputs charts ht routes)
    (z : Plane) (hz : z∈x.trace) (hd : z∈C.hostDisk v) : z=C.port x.dart.val x.parameter := by
  obtain ⟨a,_,hx⟩ := List.mem_flatMap.mp hx
  rcases C.rootArrivalBlock_cases charts ht routes a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_⟩
  · exact C.childArrivals_contact charts ht routes c hc x hx z hz hd
  · exact Set.mem_singleton_iff.mp hz

theorem rootOutputs_support (x : C.PortArrival v) (hx : x∈C.rootOutputs charts ht routes) :
    x.trace⊆C.clippedRegion {u | u∈(RootedOccurrenceTree.node v children).vertices}
      {e | e∈(RootedOccurrenceTree.node v children).edges} := by
  obtain ⟨a,_,hx⟩ := List.mem_flatMap.mp hx
  rcases C.rootArrivalBlock_cases charts ht routes a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_⟩
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

theorem rootOutputs_contact_band (x : C.PortArrival v) (hx : x∈C.rootOutputs charts ht routes)
    (e : E) (he : e∉(RootedOccurrenceTree.node v children).edges)
    (z : Plane) (hz : z∈x.trace) (hze : z∈Set.range (C.band Function.injective_id e)) : z=C.port x.label 0 := by
  obtain ⟨a,_,hx⟩ := List.mem_flatMap.mp hx
  rcases C.rootArrivalBlock_cases charts ht routes a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_⟩
  · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    simp only [PortArrival.castHost_trace,PortArrival.castHost_label] at *
    apply (routes c hc).contact_band y hy e _ z hz hze
    intro hem
    apply he
    rw [edges_node]
    exact List.mem_flatMap.mpr ⟨c,hc,hem⟩
  · exact Set.mem_singleton_iff.mp hz

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
