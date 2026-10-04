import PlanarHom.ColoringTestMacroSpatialCheck128_4
noncomputable section
namespace PlanarHom.ColoringTestMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
theorem edge_separated : edgeTree.selfApart (edgePairCheck graph point)=true := self128_339
theorem edge_avoids : edgeTree.apart (edgeVertexCheck graph point) vertexTree=true := apart128_ev_402
end PlanarHom.ColoringTestMacroCoordinates
