import PlanarHom.ColoringWireMacroRank
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem edge_lookup : ∀ e,edgeTree.lookup (edgePath e)=some e := by decide +kernel

theorem vertex_lookup : ∀ v,vertexTree.lookup (vertexPath v)=some v := by decide +kernel
end PlanarHom.ColoringWireMacroCoordinates
