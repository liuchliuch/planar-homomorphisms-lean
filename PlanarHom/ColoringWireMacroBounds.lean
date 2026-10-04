import PlanarHom.ColoringWireMacroRank
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem edge_nondegenerate : ∀ e,point (graph.src e)≠point (graph.dst e) := by decide +kernel

theorem edge_bounds : edgeTree.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem vertex_bounds : vertexTree.bounds (vertexBoundCheck point)=true := by decide +kernel
end PlanarHom.ColoringWireMacroCoordinates
