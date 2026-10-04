import PlanarHom.ColoringFanMacroBoundParts8
import PlanarHom.IntegerDrawingBoundsComposition
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem vertexNode_1871_bounds : vertexNode_1871.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_1904_bounds : vertexNode_1904.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_1905_bounds : vertexNode_1905.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1871_bounds vertexNode_1904_bounds

theorem vertexNode_1936_bounds : vertexNode_1936.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_1969_bounds : vertexNode_1969.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_1970_bounds : vertexNode_1970.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1936_bounds vertexNode_1969_bounds

theorem vertexNode_1971_bounds : vertexNode_1971.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1905_bounds vertexNode_1970_bounds

theorem vertexNode_2002_bounds : vertexNode_2002.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2035_bounds : vertexNode_2035.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2036_bounds : vertexNode_2036.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2002_bounds vertexNode_2035_bounds

theorem vertexNode_2067_bounds : vertexNode_2067.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2100_bounds : vertexNode_2100.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2101_bounds : vertexNode_2101.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2067_bounds vertexNode_2100_bounds

theorem vertexNode_2102_bounds : vertexNode_2102.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2036_bounds vertexNode_2101_bounds

theorem vertexNode_2103_bounds : vertexNode_2103.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1971_bounds vertexNode_2102_bounds

theorem vertexNode_2104_bounds : vertexNode_2104.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1840_bounds vertexNode_2103_bounds

theorem vertexNode_2105_bounds : vertexNode_2105.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1577_bounds vertexNode_2104_bounds

theorem vertexNode_2106_bounds : vertexNode_2106.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1052_bounds vertexNode_2105_bounds

end PlanarHom.ColoringFanMacroCoordinates
