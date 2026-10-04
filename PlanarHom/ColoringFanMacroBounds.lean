import PlanarHom.ColoringFanMacroBoundParts9
import PlanarHom.ColoringFanMacroRankChunks
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem endpoints_ne : ∀e,graph.src e≠graph.dst e := by decide +kernel
 theorem edge_nondegenerate (e : Edge) : point (graph.src e)≠point (graph.dst e) := by
  intro h
  have hv := congrArg coordinateRank h
  simp only [rank_point] at hv
  exact endpoints_ne e (Fin.ext hv)
 theorem edge_bounds : edgeTree.bounds (edgeBoundCheck graph point)=true := edgeNode_5236_bounds
 theorem vertex_bounds : vertexTree.bounds (vertexBoundCheck point)=true := vertexNode_2106_bounds
end PlanarHom.ColoringFanMacroCoordinates
