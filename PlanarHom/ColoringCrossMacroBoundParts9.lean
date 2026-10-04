import PlanarHom.ColoringCrossMacroBoundParts8
import PlanarHom.IntegerDrawingBoundsComposition
noncomputable section
namespace PlanarHom.ColoringCrossMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem vertexNode_2215_bounds : vertexNode_2215.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2216_bounds : vertexNode_2216.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2176_bounds vertexNode_2215_bounds

theorem vertexNode_2217_bounds : vertexNode_2217.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2137_bounds vertexNode_2216_bounds

theorem vertexNode_2218_bounds : vertexNode_2218.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2058_bounds vertexNode_2217_bounds

theorem vertexNode_2255_bounds : vertexNode_2255.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2294_bounds : vertexNode_2294.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2295_bounds : vertexNode_2295.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2255_bounds vertexNode_2294_bounds

theorem vertexNode_2334_bounds : vertexNode_2334.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2373_bounds : vertexNode_2373.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2374_bounds : vertexNode_2374.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2334_bounds vertexNode_2373_bounds

theorem vertexNode_2375_bounds : vertexNode_2375.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2295_bounds vertexNode_2374_bounds

theorem vertexNode_2414_bounds : vertexNode_2414.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2453_bounds : vertexNode_2453.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2454_bounds : vertexNode_2454.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2414_bounds vertexNode_2453_bounds

theorem vertexNode_2493_bounds : vertexNode_2493.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2532_bounds : vertexNode_2532.bounds (vertexBoundCheck point)=true := by decide +kernel

theorem vertexNode_2533_bounds : vertexNode_2533.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2493_bounds vertexNode_2532_bounds

theorem vertexNode_2534_bounds : vertexNode_2534.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2454_bounds vertexNode_2533_bounds

theorem vertexNode_2535_bounds : vertexNode_2535.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2375_bounds vertexNode_2534_bounds

theorem vertexNode_2536_bounds : vertexNode_2536.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_2218_bounds vertexNode_2535_bounds

theorem vertexNode_2537_bounds : vertexNode_2537.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1901_bounds vertexNode_2536_bounds

theorem vertexNode_2538_bounds : vertexNode_2538.bounds (vertexBoundCheck point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) vertexNode_1268_bounds vertexNode_2537_bounds

end PlanarHom.ColoringCrossMacroCoordinates
