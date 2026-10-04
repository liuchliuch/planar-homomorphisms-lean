import PlanarHom.RootedOccurrenceTreeLookup
import PlanarHom.OccurrenceKasteleynLocalLaneFamily

/-! NEW exact finite port-word derivations for recursive geometric routing.
These retain every order choice in the literal host-row expansion. They are
pure list/tree statements and make no assertion about planar arcs or LR sides. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable (charts : ∀ v, HostFanChart F v)

def childWordBlock {v : V} (children : List (E × RootedOccurrenceTree V E))
    (words : ∀ c∈children, List (Dart E)) (omittedEdge : Option E) (a : HostDart G v) : List (Dart E) := by
  classical
  exact if omittedEdge=some a.val.1 then [] else
    if hc : ∃ t, (a.val.1,t)∈children then
      words (a.val.1,Classical.choose hc) (Classical.choose_spec hc)
    else [a.val]

def nodeWordExpansion (v : V) (children : List (E × RootedOccurrenceTree V E))
    (words : ∀ c∈children, List (Dart E)) (parent : E) (hdst : G.dst parent=v) : List (Dart E) := by
  classical
  exact afterParentInputs (charts v).row ⟨(parent,false),hdst⟩ (childWordBlock children words (some parent))

def rootWordExpansion (v : V) (children : List (E × RootedOccurrenceTree V E))
    (words : ∀ c∈children, List (Dart E)) : List (Dart E) :=
  (charts v).row.flatMap (childWordBlock children words none)

inductive BranchWord : RootedOccurrenceTree V E → E → List (Dart E) → Prop where
  | node (v : V) (children : List (E × RootedOccurrenceTree V E))
      (words : ∀ c∈children, List (Dart E)) (parent : E) (hdst : G.dst parent=v)
      (children_match : ∀ c hc, BranchWord c.2 c.1 (words c hc)) :
      BranchWord (.node v children) parent (nodeWordExpansion charts v children words parent hdst)

inductive RootWord : RootedOccurrenceTree V E → List (Dart E) → Prop where
  | node (v : V) (children : List (E × RootedOccurrenceTree V E))
      (words : ∀ c∈children, List (Dart E))
      (children_match : ∀ c hc, BranchWord charts c.2 c.1 (words c hc)) :
      RootWord (.node v children) (rootWordExpansion charts v children words)

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
