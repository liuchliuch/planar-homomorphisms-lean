import PlanarHom.OccurrenceKasteleynRootPortNoninterleaving
import PlanarHom.PlanarityLRRootedTreeComponents

/-! NEW ordinary-raw-input specialization of the completed geometric tree
transport. One drawing, clipping, and geometric row system serve every actual
computed DFS component simultaneously. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.PlanarityLRDirect
open Complexity MultiGraph Kasteleyn PolygonalDrawing.TwoSidedStripData

theorem exists_computedRootCircleRoutings (g : MixedCode) {bt ut : ℕ}
    (hp : g.PlanarValid bt ut) (positive : Bool) :
    ∃ d : PolygonalDrawing (dfsGraph g hp.1), ∃ D : d.refineSingle.TwoSidedStripData,
      ∃ rays : Dart (Fin g.edges.length) → Plane, (∀ a, rays a≠0) ∧
      ∃ F : ∀ a, D.EndpointFan positive a (rays a),
      ∃ C : CircleClipping F (ContinuousMap.id I),
      ∃ charts : ∀ v, HostFanChart F v,
        ∀ v : Fin g.vertices, Nonempty (C.RootRouting charts (dfsComponentTree g hp.1 v)) := by
  have hplanar := dfsGraph_planar g hp.1 ((MixedCode.planarValid_iff g hp.1).mp hp)
  obtain ⟨d,D,rays,hne,F,C,⟨charts⟩⟩ := hplanar.exists_circlePortRows positive
  refine ⟨d,D,rays,hne,F,C,charts,?_⟩
  intro v
  exact C.exists_rootRouting charts (dfsComponentTree g hp.1 v) (dfsComponentTree_valid g hp.1 v)

end PlanarHom.PlanarityLRDirect
