import PlanarHom.OccurrenceKasteleynTreeRoutingConstruction
import PlanarHom.OccurrenceKasteleynRootRoutingLabels
import PlanarHom.OccurrenceKasteleynRootReturnPaths

/-! NEW completed root-circle transport for a whole finite occurrence tree.
All branch paths and all local/root words are constructed from the actual
drawing's clipped bands, disks, and geometric rows. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (C : CircleClipping F (ContinuousMap.id I)) (charts : ∀ v, HostFanChart F v)

def nodeRootRouting {v : V} {children : List (E × RootedOccurrenceTree V E)}
    (ht : (RootedOccurrenceTree.node v children).Valid G)
    (routes : ∀ c∈children, C.RoutedBranch charts c.2 c.1) :
    C.RootRouting charts (RootedOccurrenceTree.node v children) where
  outputs := C.rootOutputs charts ht routes
  word := by
    have hh := RootWord.node (charts:=charts) v children
      (fun c hc => (routes c hc).outputs.map PortArrival.label) (fun c hc => (routes c hc).word)
    exact (C.rootOutputs_label_word charts ht routes).symm ▸ hh
  ordered := C.rootOutputs_ordered charts ht routes
  simple := C.rootOutputs_simple charts ht routes
  separated := C.rootOutputs_separated charts ht routes
  support := C.rootOutputs_support charts ht routes
  labels := C.rootOutputs_labels charts ht routes
  contact_root := C.rootOutputs_contact_root charts ht routes
  contact_band := C.rootOutputs_contact_band charts ht routes

/-- Every actual clipped drawing of a finite ordinary occurrence tree admits
the constructed exterior root-circle port transport, with its exact word. -/
theorem exists_rootRouting (tree : RootedOccurrenceTree V E) (ht : tree.Valid G) :
    Nonempty (C.RootRouting charts tree) := by
  classical
  cases tree with
  | node v children =>
      have hchild (c : E × RootedOccurrenceTree V E) (hc : c∈children) :
          Nonempty (C.RoutedBranch charts c.2 c.1) := by
        apply C.exists_routedBranch charts c.2 (child_valid ht c hc) c.1 ((compatible_node _ _).mp ht.1 c hc).2.1
        rw [((compatible_node _ _).mp ht.1 c hc).1]
        exact root_notMem_child ht c hc
      exact ⟨C.nodeRootRouting charts ht (fun c hc => Classical.choice (hchild c hc))⟩

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

namespace PlanarHom.MultiGraph
open Kasteleyn PolygonalDrawing.TwoSidedStripData
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

/-- Ordinary finite planarity supplies the actual whole-tree root-circle
transport; the finite occurrence tree is the only combinatorial input. -/
theorem Planar.exists_rootCircleRouting (h : G.Planar) (positive : Bool)
    (tree : RootedOccurrenceTree V E) (ht : tree.Valid G) :
    ∃ d : PolygonalDrawing G, ∃ D : d.refineSingle.TwoSidedStripData,
      ∃ rays : Dart E → Plane, (∀ a, rays a≠0) ∧
      ∃ F : ∀ a, D.EndpointFan positive a (rays a),
      ∃ C : CircleClipping F (ContinuousMap.id I),
      ∃ charts : ∀ v, HostFanChart F v, Nonempty (C.RootRouting charts tree) := by
  obtain ⟨d,D,rays,hne,F,C,⟨charts⟩⟩ := h.exists_circlePortRows positive
  exact ⟨d,D,rays,hne,F,C,charts,C.exists_rootRouting charts tree ht⟩

end PlanarHom.MultiGraph
