import PlanarHom.OccurrenceKasteleynTreeRoutingLabels
import PlanarHom.OccurrenceKasteleynRootRouting

/-! NEW exact original-label coverage and order for the actual root outputs. -/
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

theorem rootArrivalBlock_label_word (a : HostDart G v) :
    (C.rootArrivalBlock charts ht routes a).map PortArrival.label =
      childWordBlock children (fun c hc => (routes c hc).outputs.map PortArrival.label) none a := by
  classical
  unfold rootArrivalBlock childWordBlock
  simp only [reduceCtorEq,if_false]
  split_ifs <;> simp only [List.map_singleton,PortArrival.localPort,C.childArrivals_label_word]

theorem rootOutputs_label_word :
    (C.rootOutputs charts ht routes).map PortArrival.label =
      rootWordExpansion charts v children (fun c hc => (routes c hc).outputs.map PortArrival.label) := by
  rw [rootOutputs,List.map_flatMap]
  unfold rootWordExpansion
  congr 1
  funext a
  exact C.rootArrivalBlock_label_word charts ht routes a

theorem rootArrivalBlock_eq_child (c : E×RootedOccurrenceTree V E)
    (hc : c∈children) (a : HostDart G v) (he : a.val.1=c.1) :
    C.rootArrivalBlock charts ht routes a=C.childArrivals charts ht routes c hc := by
  classical
  unfold rootArrivalBlock
  have hm : ∃t,(a.val.1,t)∈children := ⟨c.2,he.symm ▸ hc⟩
  rw [dif_pos hm]
  have hpair : (a.val.1,Classical.choose hm)=c :=
    child_unique ht (Classical.choose_spec hm) hc he
  cases hpair
  rfl

include ht in
theorem child_boundary_avoids_root_edges (c : E×RootedOccurrenceTree V E) (hc : c∈children)
    (a : Dart E) (hhost : (G.dartPair a).1∈c.2.vertices) (hedge : a.1∉c.1::c.2.edges) :
    a.1∉(node v children).edges := by
  intro he
  rw [edges_node] at he
  obtain ⟨k,hk,he⟩:=List.mem_flatMap.mp he
  by_cases hck:c=k
  · subst k
    exact hedge he
  · have hdis: c.2.vertices.Disjoint k.2.vertices :=
      (child_vertices_disjoint ht).forall (fun _ _ h=>h.symm) hc hk hck
    have hends:=branch_endpoints ht k hk a.1 he
    rcases dart_host_endpoints (G:=G) a with hs | hd
    · rcases hends.1 with hs' | hs'
      · exact root_notMem_child ht c hc ((hs.trans hs') ▸ hhost)
      · exact hdis hhost (hs.symm ▸ hs')
    · exact hdis hhost (hd.symm ▸ hends.2)

theorem rootArrivalBlock_labels (a : Dart E) :
    (∃ b : HostDart G v, ∃x∈C.rootArrivalBlock charts ht routes b,x.label=a) ↔
    (G.dartPair a).1∈(RootedOccurrenceTree.node v children).vertices ∧
      a.1∉(RootedOccurrenceTree.node v children).edges := by
  classical
  constructor
  · rintro ⟨b,x,hx,rfl⟩
    rcases C.rootArrivalBlock_cases charts ht routes b x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,hn⟩
    · have hs := (C.childArrivals_labels charts ht routes c hc x.label).mp (List.mem_map.mpr ⟨x,hx,rfl⟩)
      exact ⟨child_vertex_mem_node c hc hs.1,child_boundary_avoids_root_edges ht c hc x.label hs.1 hs.2⟩
    · refine ⟨b.property.symm ▸ (node v children).root_mem_vertices,?_⟩
      intro he
      obtain ⟨u,hu,_⟩ := (incident_tree_dart_iff_lookup _ ht b.val).mp ⟨he,b.property⟩
      exact hn u ((childLookup_eq_some_iff _ ht _ _).mp hu)
  · rintro ⟨hh,he⟩
    rw [vertices_node] at hh
    rcases List.mem_cons.mp hh with hh | hh
    · let b : HostDart G v := ⟨a,hh⟩
      refine ⟨b,PortArrival.localPort b,?_,rfl⟩
      have hc : ¬∃t,(a.1,t)∈children := by
        rintro ⟨t,htm⟩
        exact he (child_branch_edge_mem_node (a.1,t) htm (List.mem_cons_self ..))
      simp only [rootArrivalBlock,b,dif_neg hc,List.mem_singleton]
    · obtain ⟨c,hc,hh⟩:=List.mem_flatMap.mp hh
      have hedge : a.1∉c.1::c.2.edges := fun hm => he (child_branch_edge_mem_node c hc hm)
      obtain ⟨x,hx,hl⟩ := List.mem_map.mp ((C.childArrivals_labels charts ht routes c hc a).mpr ⟨hh,hedge⟩)
      let b : HostDart G v := ⟨(c.1,true),((compatible_node _ _).mp ht.1 c hc).1⟩
      refine ⟨b,x,?_,hl⟩
      rw [C.rootArrivalBlock_eq_child charts ht routes c hc b rfl]
      exact hx

theorem rootOutputs_labels (a : Dart E) :
    a∈(C.rootOutputs charts ht routes).map PortArrival.label ↔
      (G.dartPair a).1∈(RootedOccurrenceTree.node v children).vertices ∧
      a.1∉(RootedOccurrenceTree.node v children).edges := by
  rw [← C.rootArrivalBlock_labels charts ht routes a]
  simp only [rootOutputs,List.mem_map,List.mem_flatMap]
  constructor
  · rintro ⟨x,⟨b,_,hx⟩,he⟩
    exact ⟨b,x,hx,he⟩
  · rintro ⟨b,x,hx,he⟩
    exact ⟨x,⟨b,(charts v).mem_row b,hx⟩,he⟩

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
