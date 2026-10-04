import PlanarHom.OccurrenceKasteleynTreeRoutingStep
import PlanarHom.RootedOccurrenceTreeBoundaryLabels
import PlanarHom.OccurrenceKasteleynArrivalLabelCoverage

/-! NEW exact label coverage and word order for the concrete routed node. -/
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

theorem childArrivals_label_word (c : E×RootedOccurrenceTree V E) (hc : c∈children) :
    (C.childArrivals charts ht routes c hc).map PortArrival.label =
      (routes c hc).outputs.map PortArrival.label := by
  simp only [childArrivals,List.map_map,Function.comp_def,PortArrival.castHost_label]

theorem childArrivals_labels (c : E×RootedOccurrenceTree V E) (hc : c∈children) (a : Dart E) :
    a∈(C.childArrivals charts ht routes c hc).map PortArrival.label ↔
      (G.dartPair a).1∈c.2.vertices ∧ a.1∉c.1::c.2.edges := by
  rw [C.childArrivals_label_word charts ht routes c hc]
  exact (routes c hc).labels a

theorem nodeArrivalBlock_label_word (parent : E) (a : HostDart G v) :
    (C.nodeArrivalBlock charts ht routes parent a).map PortArrival.label =
      childWordBlock children (fun c hc => (routes c hc).outputs.map PortArrival.label) (some parent) a := by
  classical
  unfold nodeArrivalBlock childWordBlock
  simp only [Option.some.injEq,eq_comm (a:=parent) (b:=a.val.1)]
  split_ifs <;> simp only [List.map_nil,List.map_singleton,PortArrival.localPort,
    C.childArrivals_label_word]

theorem nodeOutputs_label_word (parent : E) (hdst : G.dst parent=v)
    (hsrc : G.src parent∉(RootedOccurrenceTree.node v children).vertices) :
    (C.nodeOutputs charts ht routes parent hdst hsrc).map PortArrival.label =
      nodeWordExpansion charts v children (fun c hc => (routes c hc).outputs.map PortArrival.label) parent hdst := by
  classical
  rw [nodeOutputs,C.routedArrivals_label_word]
  unfold nodeWordExpansion
  congr 1
  funext a
  exact C.nodeArrivalBlock_label_word charts ht routes parent a

theorem nodeArrivalBlock_eq_child (parent : E) (c : E×RootedOccurrenceTree V E)
    (hc : c∈children) (a : HostDart G v) (he : a.val.1=c.1) (hp : a.val.1≠parent) :
    C.nodeArrivalBlock charts ht routes parent a=C.childArrivals charts ht routes c hc := by
  classical
  unfold nodeArrivalBlock
  rw [if_neg hp]
  have hm : ∃t,(a.val.1,t)∈children := ⟨c.2,he.symm ▸ hc⟩
  rw [dif_pos hm]
  have hpair : (a.val.1,Classical.choose hm)=c :=
    child_unique ht (Classical.choose_spec hm) hc he
  cases hpair
  rfl

theorem nodeArrivalBlock_labels (parent : E) (hdst : G.dst parent=v)
    (hsrc : G.src parent∉(RootedOccurrenceTree.node v children).vertices) (a : Dart E) :
    (∃ b : HostDart G v, ∃x∈C.nodeArrivalBlock charts ht routes parent b,x.label=a) ↔
    (G.dartPair a).1∈(RootedOccurrenceTree.node v children).vertices ∧
      a.1∉parent::(RootedOccurrenceTree.node v children).edges := by
  classical
  constructor
  · rintro ⟨b,x,hx,rfl⟩
    rcases C.nodeArrivalBlock_cases charts ht routes parent b x hx with ⟨c,hc,_,hx⟩ | ⟨rfl,hp,hn⟩
    · have hs := (C.childArrivals_labels charts ht routes c hc x.label).mp (List.mem_map.mpr ⟨x,hx,rfl⟩)
      exact ⟨child_vertex_mem_node c hc hs.1,child_boundary_avoids_node ht parent hdst hsrc c hc x.label hs.1 hs.2⟩
    · refine ⟨b.property.symm ▸ (node v children).root_mem_vertices,?_⟩
      intro he
      rcases List.mem_cons.mp he with he | he
      · exact hp he
      · obtain ⟨u,hu,_⟩ := (incident_tree_dart_iff_lookup _ ht b.val).mp ⟨he,b.property⟩
        exact hn u ((childLookup_eq_some_iff _ ht _ _).mp hu)
  · rintro ⟨hh,he⟩
    rw [vertices_node] at hh
    rcases List.mem_cons.mp hh with hh | hh
    · let b : HostDart G v := ⟨a,hh⟩
      refine ⟨b,PortArrival.localPort b,?_,rfl⟩
      have hp : a.1≠parent := fun h => he (List.mem_cons.mpr (Or.inl h))
      have hc : ¬∃t,(a.1,t)∈children := by
        rintro ⟨t,htm⟩
        exact he (List.mem_cons_of_mem _ (child_branch_edge_mem_node (a.1,t) htm (List.mem_cons_self ..)))
      simp only [nodeArrivalBlock,b,hp,if_false,dif_neg hc,List.mem_singleton]
    · obtain ⟨c,hc,hh⟩:=List.mem_flatMap.mp hh
      have hedge : a.1∉c.1::c.2.edges := fun hm =>
        he (List.mem_cons_of_mem _ (child_branch_edge_mem_node c hc hm))
      obtain ⟨x,hx,hl⟩ := List.mem_map.mp ((C.childArrivals_labels charts ht routes c hc a).mpr ⟨hh,hedge⟩)
      let b : HostDart G v := ⟨(c.1,true),((compatible_node _ _).mp ht.1 c hc).1⟩
      refine ⟨b,x,?_,hl⟩
      rw [C.nodeArrivalBlock_eq_child charts ht routes parent c hc b rfl
        (child_edge_ne_external_parent ht parent hsrc c hc)]
      exact hx

theorem nodeRoutedArrivals_labels (parent : E) (hdst : G.dst parent=v)
    (hsrc : G.src parent∉(RootedOccurrenceTree.node v children).vertices) (a : Dart E) :
    a∈(C.nodeOutputs charts ht routes parent hdst hsrc).map PortArrival.label ↔
      (G.dartPair a).1∈(RootedOccurrenceTree.node v children).vertices ∧
      a.1∉parent::(RootedOccurrenceTree.node v children).edges := by
  classical
  rw [nodeOutputs,C.mem_routedArrivals_labels]
  · exact C.nodeArrivalBlock_labels charts ht routes parent hdst hsrc a
  · simp [nodeArrivalBlock]

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
