import PlanarHom.ColoringFanMacroRankChunks
import PlanarHom.ColoringFanMacroLookup
import PlanarHom.ColoringFanMacroBounds
import PlanarHom.ColoringFanMacroSeparation
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate

theorem points_injective : Function.Injective point := by
  intro v w h
  apply Fin.ext
  simpa only [rank_point] using congrArg coordinateRank h

def spatialCertificate : IntegerDrawingSpatialCertificate.Certificate graph point where
  injective := points_injective
  nondegenerate := edge_nondegenerate
  edges := edgeTree
  vertices := vertexTree
  edgePath := edgePath
  vertexPath := vertexPath
  edgeLookup := edge_lookup
  vertexLookup := vertex_lookup
  edgeBounds := edge_bounds
  vertexBounds := vertex_bounds
  separated := edge_separated
  avoids := edge_avoids

def drawing : PlaneDrawing graph := spatialCertificate.drawing

theorem planar : graph.Planar := ⟨drawing⟩
end PlanarHom.ColoringFanMacroCoordinates
