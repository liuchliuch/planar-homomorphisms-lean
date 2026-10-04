import PlanarHom.ColoringWireMacroRank
import PlanarHom.ColoringWireMacroBounds
import PlanarHom.ColoringWireMacroLookup
import PlanarHom.ColoringWireMacroSeparation

/-! Actual fixed wire macro drawing assembled only from the bounded,
kernel-checked coordinate, coverage, and spatial separation certificates. -/
noncomputable section
namespace PlanarHom.ColoringWireMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate

theorem points_injective : Function.Injective point := by
  intro v w h
  have hh := congrArg coordinateRank h
  simpa only [rank_point] using hh

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
end PlanarHom.ColoringWireMacroCoordinates
