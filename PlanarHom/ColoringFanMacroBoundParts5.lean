import PlanarHom.ColoringFanMacroBoundParts4
import PlanarHom.IntegerDrawingBoundsComposition
noncomputable section
namespace PlanarHom.ColoringFanMacroCoordinates
open MultiGraph IntegerStraightDrawing IntegerDrawingSpatialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem edgeNode_4206_bounds : edgeNode_4206.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4247_bounds : edgeNode_4247.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4248_bounds : edgeNode_4248.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4206_bounds edgeNode_4247_bounds

theorem edgeNode_4249_bounds : edgeNode_4249.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4167_bounds edgeNode_4248_bounds

theorem edgeNode_4250_bounds : edgeNode_4250.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4086_bounds edgeNode_4249_bounds

theorem edgeNode_4289_bounds : edgeNode_4289.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4330_bounds : edgeNode_4330.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4331_bounds : edgeNode_4331.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4289_bounds edgeNode_4330_bounds

theorem edgeNode_4370_bounds : edgeNode_4370.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4411_bounds : edgeNode_4411.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4412_bounds : edgeNode_4412.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4370_bounds edgeNode_4411_bounds

theorem edgeNode_4413_bounds : edgeNode_4413.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4331_bounds edgeNode_4412_bounds

theorem edgeNode_4452_bounds : edgeNode_4452.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4493_bounds : edgeNode_4493.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4494_bounds : edgeNode_4494.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4452_bounds edgeNode_4493_bounds

theorem edgeNode_4533_bounds : edgeNode_4533.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4574_bounds : edgeNode_4574.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4575_bounds : edgeNode_4575.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4533_bounds edgeNode_4574_bounds

theorem edgeNode_4576_bounds : edgeNode_4576.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4494_bounds edgeNode_4575_bounds

theorem edgeNode_4577_bounds : edgeNode_4577.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4413_bounds edgeNode_4576_bounds

theorem edgeNode_4578_bounds : edgeNode_4578.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4250_bounds edgeNode_4577_bounds

theorem edgeNode_4617_bounds : edgeNode_4617.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4658_bounds : edgeNode_4658.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4659_bounds : edgeNode_4659.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4617_bounds edgeNode_4658_bounds

theorem edgeNode_4698_bounds : edgeNode_4698.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4739_bounds : edgeNode_4739.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4740_bounds : edgeNode_4740.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4698_bounds edgeNode_4739_bounds

theorem edgeNode_4741_bounds : edgeNode_4741.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4659_bounds edgeNode_4740_bounds

theorem edgeNode_4780_bounds : edgeNode_4780.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4821_bounds : edgeNode_4821.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4822_bounds : edgeNode_4822.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4780_bounds edgeNode_4821_bounds

theorem edgeNode_4861_bounds : edgeNode_4861.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4902_bounds : edgeNode_4902.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4903_bounds : edgeNode_4903.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4861_bounds edgeNode_4902_bounds

theorem edgeNode_4904_bounds : edgeNode_4904.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4822_bounds edgeNode_4903_bounds

theorem edgeNode_4905_bounds : edgeNode_4905.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4741_bounds edgeNode_4904_bounds

theorem edgeNode_4944_bounds : edgeNode_4944.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4985_bounds : edgeNode_4985.bounds (edgeBoundCheck graph point)=true := by decide +kernel

theorem edgeNode_4986_bounds : edgeNode_4986.bounds (edgeBoundCheck graph point)=true := IntegerDrawingSpatialCertificate.Tree.bounds_node (by decide +kernel) (by decide +kernel) edgeNode_4944_bounds edgeNode_4985_bounds

theorem edgeNode_5025_bounds : edgeNode_5025.bounds (edgeBoundCheck graph point)=true := by decide +kernel

end PlanarHom.ColoringFanMacroCoordinates
