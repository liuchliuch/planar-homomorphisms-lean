import PlanarHom.PlanarColoringOneWayConverter
import PlanarHom.IntegerStraightDrawing

/-! An independently checked literal planar drawing of the entire 34-vertex,
76-edge palette-propagating one-way converter. Integer coordinates were found
by solving a rational barycentric system and rounding; that search is untrusted.
The finite certificate below is checked entirely by Lean's kernel. -/
noncomputable section
namespace PlanarHom.PlanarColoringOneWayConverter
open MultiGraph
set_option maxHeartbeats 20000000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 10000

def integerPoint : Fin 34 → IntegerStraightDrawing.Point :=
  ![(-40,0),(40,0),(-20,30),(-17,3),(20,30),(2,-3),(-20,-30),(20,-30),
    (-15,-13),(4,-16),(15,-12),(-23,-10),(10,-15),(-4,15),(-5,-9),(-3,-12),
    (-7,-14),(-10,-23),(-13,-20),(-9,-17),(-4,-11),(-11,-21),(-2,-8),(-14,-23),
    (20,-18),(25,-11),(23,-6),(27,13),(21,6),(23,1),(22,-14),(23,9),(22,-18),(23,15)]

/-- Exact decidable finite geometry; no imported planarity oracle or drawing
correctness assumption participates in this proof. -/
def integerCertificate : IntegerStraightDrawing.Certificate graph integerPoint where
  injective := by decide
  nondegenerate := by decide
  separated := by decide
  avoids := by decide

def drawing : PlaneDrawing graph := IntegerStraightDrawing.drawing integerCertificate

theorem planar : graph.Planar := ⟨drawing⟩

/-- Primary and palette ports lie on the boundary in the required clockwise
order: x, upper-black, upper-gray, x', lower-black, lower-gray. -/
theorem port_coordinates :
    integerPoint 0=(-40,0) ∧ integerPoint 2=(-20,30) ∧ integerPoint 4=(20,30) ∧
    integerPoint 1=(40,0) ∧ integerPoint 7=(20,-30) ∧ integerPoint 6=(-20,-30) := by decide

theorem nonport_coordinates : ∀ v : Fin 34, v≠0 → v≠1 → v≠2 → v≠4 → v≠6 → v≠7 →
    -40<(integerPoint v).1 ∧ (integerPoint v).1<40 ∧
    -30<(integerPoint v).2 ∧ (integerPoint v).2<30 := by decide

end PlanarHom.PlanarColoringOneWayConverter
