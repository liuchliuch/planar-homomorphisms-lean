import PlanarHom.SignedNandCellGraphs
import PlanarHom.IntegerDrawingBox
import PlanarHom.PlaneDrawingUnsubdivide

/-! Actual fixed drawings on precisely the existing macro-cell signal ports.
The test K4 has polygonal edges; its bends introduce no graph vertices. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.SignedNandCells
open PositiveBlockProgram MultiGraph IntegerStraightDrawing
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def testPoint : Vertex .test ⊕ Fin 6 → Point :=
  Sum.elim (point .test) ![(8,96),(8,32),(60,64),(16,96),(16,64),(16,32)]

def testCertificate : Certificate (graph .test).subdivide testPoint where
  injective := by decide
  nondegenerate := by decide
  separated := by decide
  avoids := by decide

def testDrawing : PlaneDrawing (graph .test) := (IntegerStraightDrawing.drawing testCertificate).unsubdivide

def drawing : (s : CellShape) → PlaneDrawing (graph s.kind)
  | .wireTop => straightDrawing .wireTop (by decide)
  | .wireBottom => straightDrawing .wireBottom (by decide)
  | .wireDown => straightDrawing .wireDown (by decide)
  | .cross => straightDrawing .cross (by decide)
  | .fan => straightDrawing .fan (by decide)
  | .test => testDrawing

@[simp] theorem drawing_point (s : CellShape) (v : Vertex s.kind) :
    (drawing s).point v=toPlane (point s v) := by cases s <;> rfl

theorem port_points (s : CellShape) : ∀i,point s (.inl (s.portVertex i))=s.portPoint i := by
  cases s <;> decide

theorem auxiliaries_inside (s : CellShape) : ∀v,s.portCount≤v.val→
    OpenBox (64*s.height) (point s (.inl v)) := by cases s <;> decide

theorem centers_inside (s : CellShape) : ∀v,OpenBox (64*s.height) (point s (.inr v)) := by
  cases s <;> decide

theorem straight_edges_box (s : CellShape) (hs : s≠.test) : ∀e,
    ClosedBox (64*s.height) (point s ((graph s.kind).src e)) ∧
    ClosedBox (64*s.height) (point s ((graph s.kind).dst e)) ∧
      (OpenBox (64*s.height) (point s ((graph s.kind).src e)) ∨
       OpenBox (64*s.height) (point s ((graph s.kind).dst e))) := by
  cases s
  all_goals first | exact False.elim (hs rfl) | decide

theorem test_edges_box : ∀e,
    ClosedBox 128 (testPoint ((graph .test).subdivide.src e)) ∧
    ClosedBox 128 (testPoint ((graph .test).subdivide.dst e)) ∧
      (OpenBox 128 (testPoint ((graph .test).subdivide.src e)) ∨
       OpenBox 128 (testPoint ((graph .test).subdivide.dst e))) := by decide

theorem straight_curves_inside (s : CellShape) (hs : s≠.test) :
    ∀e t,Inside t→(straightDrawing s hs).curve e t∈realBox (64*s.height) :=
  drawing_curve_in_box (straightCertificate s hs) (64*s.height) (straight_edges_box s hs)

theorem test_midpoints_inside : ∀e : Fin 6,OpenBox 128 (testPoint (.inr e)) := by decide

theorem curves_inside (s : CellShape) : ∀e t,Inside t→(drawing s).curve e t∈realBox (64*s.height) := by
  cases s with
  | wireTop => exact straight_curves_inside .wireTop (by decide)
  | wireBottom => exact straight_curves_inside .wireBottom (by decide)
  | wireDown => exact straight_curves_inside .wireDown (by decide)
  | cross => exact straight_curves_inside .cross (by decide)
  | fan => exact straight_curves_inside .fan (by decide)
  | test =>
    exact PlaneDrawing.unsubdivide_curve_in _ _
      (fun e => openBox_cast (test_midpoints_inside e))
      (fun e b t ht => drawing_curve_in_box testCertificate 128 test_edges_box (e,b) t ht)

end PlanarHom.SignedNandCells
