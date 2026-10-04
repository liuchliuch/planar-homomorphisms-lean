import PlanarHom.ColoringTestMacroSpatialCheck128_3
noncomputable section
namespace PlanarHom.ColoringTestMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem apart128_ev_400 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_540 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_392 apart128_ev_399

theorem apart128_ev_401 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_541 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_385 apart128_ev_400

theorem apart128_ev_402 : IntegerDrawingSpatialCertificate.Tree.apart (edgeVertexCheck graph point) edgeNode_542 vertexNode_226=true :=
  IntegerDrawingSpatialCertificate.Tree.apart_node apart128_ev_370 apart128_ev_401

end PlanarHom.ColoringTestMacroCoordinates
