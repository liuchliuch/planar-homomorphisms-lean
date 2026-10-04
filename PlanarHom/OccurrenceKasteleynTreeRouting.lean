import PlanarHom.RootedOccurrenceTreeLookup
import PlanarHom.OccurrenceKasteleynRouteArrivalBlocks
import PlanarHom.OccurrenceKasteleynTreePortWords

/-! NEW recursive whole-tree transport of original occurrence ports. The
recursive input is a finite ordinary occurrence tree with distinct vertices;
all geometric data are constructed inside the original clipped disks/bands. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) (charts : ∀ v, HostFanChart F v)

/-- Induction result for a genuine finite branch and its incoming tree edge.
The original label set and every possible external contact are explicit. -/
structure RoutedBranch (tree : RootedOccurrenceTree V E) (parent : E) where
  outputs : List (C.PortArrival (G.src parent))
  word : BranchWord charts tree parent (outputs.map PortArrival.label)
  placed : ∀ x∈outputs, x.dart.val=(parent,true)
  ordered : outputs.Pairwise (fun x y =>
    (charts (G.src parent)).height x.dart x.parameter<(charts (G.src parent)).height y.dart y.parameter)
  simple : ∀ x∈outputs, x.Simple
  separated : outputs.Pairwise (fun x y => Disjoint x.trace y.trace)
  support : ∀ x∈outputs, x.trace⊆C.branchRegion (parent,tree)
  labels : ∀ a, a∈outputs.map PortArrival.label ↔
    (G.dartPair a).1∈tree.vertices ∧ a.1∉parent::tree.edges
  contact_disk : ∀ x∈outputs, ∀ v, v∉tree.vertices → ∀ z∈x.trace, z∈C.hostDisk v →
    z=C.port x.dart.val x.parameter ∧ G.src parent=v
  contact_band : ∀ x∈outputs, ∀ e, e∉parent::tree.edges →
    ∀ z∈x.trace, z∈Set.range (C.band Function.injective_id e) → z=C.port x.label 0

namespace RoutedBranch
variable {C charts} {tree : RootedOccurrenceTree V E} {parent : E}

theorem label_spec (R : C.RoutedBranch charts tree parent) (x : C.PortArrival (G.src parent))
    (hx : x∈R.outputs) : (G.dartPair x.label).1∈tree.vertices ∧ x.label.1∉parent::tree.edges :=
  (R.labels x.label).mp (List.mem_map.mpr ⟨x,hx,rfl⟩)

theorem output_separated (R : C.RoutedBranch charts tree parent)
    {x y : C.PortArrival (G.src parent)} (hx : x∈R.outputs) (hy : y∈R.outputs) (hne : x≠y) :
    Disjoint x.trace y.trace := R.separated.forall (fun _ _ h => h.symm) hx hy hne

end RoutedBranch

variable {v : V} {children : List (E × RootedOccurrenceTree V E)}
variable (ht : (RootedOccurrenceTree.node v children).Valid G)
variable (routes : ∀ c∈children, C.RoutedBranch charts c.2 c.1)

def childArrivals (c : E × RootedOccurrenceTree V E) (hc : c∈children) : List (C.PortArrival v) :=
  (routes c hc).outputs.map (PortArrival.castHost (((compatible_node _ _).mp ht.1 c hc).1))

def nodeArrivalBlock (parent : E) (a : HostDart G v) : List (C.PortArrival v) := by
  classical
  exact if a.val.1=parent then [] else
    if h : ∃ t, (a.val.1,t)∈children then
      C.childArrivals charts ht routes (a.val.1,Classical.choose h) (Classical.choose_spec h)
    else [PortArrival.localPort a]

theorem nodeArrivalBlock_cases (parent : E) (a : HostDart G v) (x : C.PortArrival v)
    (hx : x∈C.nodeArrivalBlock charts ht routes parent a) :
    (∃ c, ∃ hc : c∈children, c.1=a.val.1 ∧ x∈C.childArrivals charts ht routes c hc) ∨
      (x=PortArrival.localPort a ∧ a.val.1≠parent ∧ ∀ t, (a.val.1,t)∉children) := by
  classical
  unfold nodeArrivalBlock at hx
  split_ifs at hx with hp hc
  · simp at hx
  · exact Or.inl ⟨_,Classical.choose_spec hc,rfl,hx⟩
  · exact Or.inr ⟨List.mem_singleton.mp hx,hp,by simpa only [not_exists] using hc⟩

theorem childArrivals_placed (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (x : C.PortArrival v) (hx : x∈C.childArrivals charts ht routes c hc) : x.dart.val=(c.1,true) := by
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  rw [PortArrival.castHost_dart]
  exact (routes c hc).placed y hy

theorem childArrivals_support (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (x : C.PortArrival v) (hx : x∈C.childArrivals charts ht routes c hc) :
    x.trace⊆C.branchRegion c := by
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  rw [PortArrival.castHost_trace]
  exact (routes c hc).support y hy

theorem childArrivals_simple (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (x : C.PortArrival v) (hx : x∈C.childArrivals charts ht routes c hc) : x.Simple := by
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  rw [PortArrival.castHost_simple]
  exact (routes c hc).simple y hy

theorem childArrivals_contact (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (x : C.PortArrival v) (hx : x∈C.childArrivals charts ht routes c hc)
    (z : Plane) (hz : z∈x.trace) (hd : z∈C.hostDisk v) : z=C.port x.dart.val x.parameter := by
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  simp only [PortArrival.castHost_trace,PortArrival.castHost_dart,PortArrival.castHost_parameter] at *
  exact ((routes c hc).contact_disk y hy v (root_notMem_child ht c hc) z hz hd).1

theorem childArrivals_separated (c : E × RootedOccurrenceTree V E) (hc : c∈children) :
    (C.childArrivals charts ht routes c hc).Pairwise (fun x y => Disjoint x.trace y.trace) := by
  simpa only [childArrivals,List.pairwise_map,PortArrival.castHost_trace] using (routes c hc).separated

theorem childArrivals_ordered (c : E × RootedOccurrenceTree V E) (hc : c∈children) :
    (C.childArrivals charts ht routes c hc).Pairwise (fun x y =>
      (charts v).height x.dart x.parameter<(charts v).height y.dart y.parameter) := by
  have hs := ((compatible_node _ _).mp ht.1 c hc).1
  have hh := (routes c hc).ordered
  unfold childArrivals
  rw [List.pairwise_map]
  cases hs
  exact hh

include ht in
theorem child_dart_eq (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (a : HostDart G v) (he : c.1=a.val.1) : a.val=(c.1,true) := by
  classical
  have hm : a.val.1∈(RootedOccurrenceTree.node v children).edges := by
    rw [edges_node,← he]
    exact List.mem_flatMap.mpr ⟨c,hc,List.mem_cons_self ..⟩
  have hb := ((incident_tree_dart_iff_lookup _ ht a.val).mp ⟨hm,a.property⟩).choose_spec.2
  exact Prod.ext he.symm hb

theorem nodeArrivalBlock_placed (parent : E) (a : HostDart G v) (x : C.PortArrival v)
    (hx : x∈C.nodeArrivalBlock charts ht routes parent a) : x.dart=a := by
  rcases C.nodeArrivalBlock_cases charts ht routes parent a x hx with ⟨c,hc,he,hx⟩ | ⟨rfl,_,_⟩
  · exact Subtype.ext ((C.childArrivals_placed charts ht routes c hc x hx).trans (child_dart_eq ht c hc a he).symm)
  · rfl

theorem port_mem_hostDisk (a : HostDart G v) (s : I) : C.port a.val s∈C.hostDisk v := by
  change rayLength (C.port a.val s-d.drawing.point v)≤C.radius
  rw [C.port_formula,a.property,add_sub_cancel_left,rayLength_smul,abs_of_pos C.radius_pos,
    normalizedFan_circle,mul_one]

theorem childArrivals_avoid_parent (parent : E) (hdst : G.dst parent=v)
    (hsrc : G.src parent∉(RootedOccurrenceTree.node v children).vertices)
    (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (x : C.PortArrival v) (hx : x∈C.childArrivals charts ht routes c hc) :
    Disjoint x.trace (Set.range (C.band Function.injective_id parent)) := by
  have he : parent∉c.1::c.2.edges := by
    intro he
    have hh := (branch_endpoints ht c hc parent he).2
    rw [hdst] at hh
    exact root_notMem_child ht c hc hh
  have hs : G.src parent∉c.2.vertices := by
    intro hh
    apply hsrc
    rw [vertices_node]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c,hc,hh⟩)
  have hd : G.dst parent∉c.2.vertices := hdst ▸ root_notMem_child ht c hc
  exact (C.clippedRegion_disjoint_band parent he hs hd).mono_left (C.childArrivals_support charts ht routes c hc x hx)

theorem child_local_disjoint (c : E × RootedOccurrenceTree V E) (hc : c∈children)
    (x : C.PortArrival v) (hx : x∈C.childArrivals charts ht routes c hc)
    (a : HostDart G v) (ha : ∀ t, (a.val.1,t)∉children) :
    Disjoint x.trace (PortArrival.localPort (C:=C) a).trace := by
  apply Set.disjoint_left.mpr
  intro z hzx hza
  have hz : z=C.port a.val 0 := Set.mem_singleton_iff.mp hza
  have he := C.childArrivals_contact charts ht routes c hc x hx z hzx (hz ▸ C.port_mem_hostDisk a 0)
  have hp := (C.port_injective (hz.symm.trans he)).1
  rw [C.childArrivals_placed charts ht routes c hc x hx] at hp
  exact ha c.2 (by simpa only [congrArg Prod.fst hp,Prod.mk.eta] using hc)

theorem nodeArrivalBlock_separated (parent : E) (a b : HostDart G v) (x y : C.PortArrival v)
    (hx : x∈C.nodeArrivalBlock charts ht routes parent a)
    (hy : y∈C.nodeArrivalBlock charts ht routes parent b) (hne : x≠y) : Disjoint x.trace y.trace := by
  rcases C.nodeArrivalBlock_cases charts ht routes parent a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_,ha⟩
  · rcases C.nodeArrivalBlock_cases charts ht routes parent b y hy with ⟨k,hk,_,hy⟩ | ⟨rfl,_,hb⟩
    · by_cases hck : c=k
      · subst k
        exact (C.childArrivals_separated charts ht routes c hc).forall (fun _ _ h => h.symm) hx hy hne
      · exact ((C.branchRegions_disjoint ht).forall (fun _ _ h => h.symm) hc hk hck).mono
          (C.childArrivals_support charts ht routes c hc x hx) (C.childArrivals_support charts ht routes k hk y hy)
    · exact C.child_local_disjoint charts ht routes c hc x hx b hb
  · rcases C.nodeArrivalBlock_cases charts ht routes parent b y hy with ⟨k,hk,_,hy⟩ | ⟨rfl,_,_⟩
    · exact (C.child_local_disjoint charts ht routes k hk y hy a ha).symm
    · apply Set.disjoint_left.mpr
      intro z hz₁ hz₂
      have he := (Set.mem_singleton_iff.mp hz₁).symm.trans (Set.mem_singleton_iff.mp hz₂)
      exact hne (congrArg PortArrival.localPort (Subtype.ext (C.port_injective he).1))

/-- Every hypothesis of the actual node router is derived from its already
routed children and its original retained local ports. -/
theorem nodeArrivalBlock_local (parent : E) (hdst : G.dst parent=v)
    (hsrc : G.src parent∉(RootedOccurrenceTree.node v children).vertices) :
    C.LocalArrivals (charts v) ⟨(parent,false),hdst⟩ (C.nodeArrivalBlock charts ht routes parent) := by
  classical
  refine ⟨?_,C.nodeArrivalBlock_placed charts ht routes parent,?_,?_,
    C.nodeArrivalBlock_separated charts ht routes parent,?_,?_⟩
  · intro he
    exact hsrc ((he.trans hdst).symm ▸ (RootedOccurrenceTree.node v children).root_mem_vertices)
  · intro a
    unfold nodeArrivalBlock
    split_ifs with hp hc
    · simp
    · apply (C.childArrivals_ordered charts ht routes _ (Classical.choose_spec hc)).imp_of_mem
      intro x y hx hy hxy
      have ha := child_dart_eq ht (a.val.1,Classical.choose hc) (Classical.choose_spec hc) a rfl
      have hxa : x.dart=a := Subtype.ext ((C.childArrivals_placed charts ht routes _ _ x hx).trans ha.symm)
      have hya : y.dart=a := Subtype.ext ((C.childArrivals_placed charts ht routes _ _ y hy).trans ha.symm)
      simpa only [hxa,hya] using hxy
    · simp
  · intro a x hx
    rcases C.nodeArrivalBlock_cases charts ht routes parent a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_,_⟩
    · exact C.childArrivals_simple charts ht routes c hc x hx
    · exact PortArrival.localPort_simple a
  · intro a x hx z hz hd
    rcases C.nodeArrivalBlock_cases charts ht routes parent a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,_,_⟩
    · exact C.childArrivals_contact charts ht routes c hc x hx z hz hd
    · exact Set.mem_singleton_iff.mp hz
  · intro a x hx
    rcases C.nodeArrivalBlock_cases charts ht routes parent a x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,he,_⟩
    · exact C.childArrivals_avoid_parent charts ht routes parent hdst hsrc c hc x hx
    · exact Set.disjoint_left.mpr (by
        intro z hz hez
        exact C.port_notMem_other_band he 0 ((Set.mem_singleton_iff.mp hz) ▸ hez))

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
