import PlanarHom.PlanarityLRGeometricWordBlocks
import PlanarHom.PlanarityLRDirectedNodeExpansion
import PlanarHom.PlanarityLRDirectedRootExpansion

/-! NEW exact identification of the constructed geometric routing word with the
actual finite permutation contour of the computed DFS tree. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch
open MultiGraph.PolygonalDrawing.TwoSidedStripData
open MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping

variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable {d : PolygonalDrawing (dfsGraph g hg)} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart (Fin g.edges.length) → Plane} (F : ∀ a, D.EndpointFan positive a (rays a))
variable (charts : ∀ v, HostFanChart F v)

/-- The exact actual child contour satisfies the same finite recursion as the
constructed paths. Recursion terminates by strictly increasing DFS depth. -/
theorem computedBranchWord (parent : Fin g.edges.length) (hp : isTree g parent.val=true) :
    BranchWord charts (dfsTree g hg (dfsTarget g hg parent)) parent
      (directedSubtreePorts g hg (dfsGeometricRows g hg F charts) parent) := by
  let rows := dfsGeometricRows g hg F charts
  let words := fun (c : Fin g.edges.length × DFSTree g)
    (_ : c∈computedChildPairs g hg (dfsTarget g hg parent)) => directedSubtreePorts g hg rows c.1
  have hchildren : ∀ c hc, BranchWord charts c.2 c.1 (words c hc) := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
    exact computedBranchWord e ((dfsChildren_mem g _ e).mp he).1
  have hstep := BranchWord.node (charts:=charts) (dfsTarget g hg parent)
    (computedChildPairs g hg (dfsTarget g hg parent)) words parent rfl hchildren
  have hword : directedSubtreePorts g hg rows parent=
      nodeWordExpansion charts (dfsTarget g hg parent)
        (computedChildPairs g hg (dfsTarget g hg parent)) words parent rfl := by
    rw [directedSubtreePorts_eq_afterParent g hg rows parent hp]
    exact (geometric_nodeWordExpansion g hg F charts parent hp
      (directedSubtreePorts g hg rows)).symm
  rw [hword,dfsTree_eq_node]
  exact hstep
termination_by g.vertices-height g (target g parent.val)
decreasing_by
  have hec := (dfsChildren_mem g (dfsTarget g hg parent) e).mp he
  have hlt := child_depth_remainder_lt g hg hec.1
  simpa only [hec.2,dfsTarget] using hlt

/-- Any geometric branch construction retaining its literal recursion has this
unique actual contour word. -/
theorem computedBranchWord_eq (parent : Fin g.edges.length) (hp : isTree g parent.val=true)
    {word : List (Dart (Fin g.edges.length))}
    (hword : BranchWord charts (dfsTree g hg (dfsTarget g hg parent)) parent word) :
    word=directedSubtreePorts g hg (dfsGeometricRows g hg F charts) parent :=
  hword.unique (computedBranchWord g hg F charts parent hp)

theorem computedRootWord (r : Fin g.vertices) (hr : height g r.val=0) :
    RootWord charts (dfsTree g hg r) (directedRootPorts g hg (dfsGeometricRows g hg F charts) r) := by
  let rows := dfsGeometricRows g hg F charts
  let words := fun (c : Fin g.edges.length × DFSTree g)
    (_ : c∈computedChildPairs g hg r) => directedSubtreePorts g hg rows c.1
  have hchildren : ∀ c hc, BranchWord charts c.2 c.1 (words c hc) := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
    exact computedBranchWord g hg F charts e ((dfsChildren_mem g _ e).mp he).1
  have hstep := RootWord.node (charts:=charts) r (computedChildPairs g hg r) words hchildren
  have hword : directedRootPorts g hg rows r=rootWordExpansion charts r (computedChildPairs g hg r) words := by
    rw [directedRootPorts_eq_row_expansion g hg rows r hr]
    exact (geometric_rootWordExpansion g hg F charts r hr (directedSubtreePorts g hg rows)).symm
  rw [hword,dfsTree_eq_node]
  exact hstep

theorem computedRootWord_eq (r : Fin g.vertices) (hr : height g r.val=0)
    {word : List (Dart (Fin g.edges.length))} (hword : RootWord charts (dfsTree g hg r) word) :
    word=directedRootPorts g hg (dfsGeometricRows g hg F charts) r :=
  hword.unique (computedRootWord g hg F charts r hr)

theorem computedComponentRootWord_eq (v : Fin g.vertices)
    {word : List (Dart (Fin g.edges.length))} (hword : RootWord charts (dfsComponentTree g hg v) word) :
    word=directedRootPorts g hg (dfsGeometricRows g hg F charts)
      ⟨componentRoot g v.val,(componentRoot_spec g v.isLt).1⟩ :=
  computedRootWord_eq g hg F charts _ (componentRoot_spec g v.isLt).2.2 hword

end PlanarHom.PlanarityLRRealization
