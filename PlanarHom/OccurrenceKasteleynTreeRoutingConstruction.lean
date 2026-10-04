import PlanarHom.OccurrenceKasteleynTreeRoutingLabels

/-! NEW completed recursive branch construction from an ordinary finite
occurrence tree and the actual clipping. No child routing, chart transport,
or port-order certificate is an input to the existence theorem. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) (charts : ∀ v, HostFanChart F v)

def nodeRoutedBranch {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (RootedOccurrenceTree.node v children).Valid G)
    (routes : ∀ c∈children, C.RoutedBranch charts c.2 c.1)
    (parent : E) (hdst : G.dst parent=v)
    (hsrc : G.src parent∉(RootedOccurrenceTree.node v children).vertices) :
    C.RoutedBranch charts (RootedOccurrenceTree.node v children) parent where
  outputs := C.nodeOutputs charts ht routes parent hdst hsrc
  word := by
    rw [C.nodeOutputs_label_word charts ht routes parent hdst hsrc]
    exact BranchWord.node v children (fun c hc => (routes c hc).outputs.map PortArrival.label)
      parent hdst (fun c hc => (routes c hc).word)
  placed := C.nodeOutputs_placed charts ht routes parent hdst hsrc
  ordered := C.nodeOutputs_ordered charts ht routes parent hdst hsrc
  simple := C.nodeOutputs_simple charts ht routes parent hdst hsrc
  separated := C.nodeOutputs_separated charts ht routes parent hdst hsrc
  support := C.nodeOutputs_support charts ht routes parent hdst hsrc
  labels := C.nodeRoutedArrivals_labels charts ht routes parent hdst hsrc
  contact_disk := C.nodeOutputs_contact_disk charts ht routes parent hdst hsrc
  contact_band := C.nodeOutputs_contact_band charts ht routes parent hdst hsrc

/-- Every finite valid occurrence branch has an actual mutually separated
family of rootward lanes, with exact recursively derived word and label set. -/
theorem exists_routedBranch (tree : RootedOccurrenceTree V E) (ht : tree.Valid G)
    (parent : E) (hdst : G.dst parent=tree.root) (hsrc : G.src parent∉tree.vertices) :
    Nonempty (C.RoutedBranch charts tree parent) := by
  classical
  induction tree using induction_children generalizing parent with
  | step v children ih =>
      have hchild (c : E × RootedOccurrenceTree V E) (hc : c∈children) :
          Nonempty (C.RoutedBranch charts c.2 c.1) := by
        apply ih c hc (child_valid ht c hc) c.1 ((compatible_node _ _).mp ht.1 c hc).2.1
        rw [((compatible_node _ _).mp ht.1 c hc).1]
        exact root_notMem_child ht c hc
      let routes := fun c hc => Classical.choice (hchild c hc)
      exact ⟨C.nodeRoutedBranch charts ht routes parent hdst hsrc⟩

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
