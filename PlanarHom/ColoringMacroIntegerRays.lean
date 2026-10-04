import PlanarHom.ColoringMacroFastEdgeBounds
import PlanarHom.PlanarityLRRealizationRotationSystem

/-! Integer representatives of the actual globally sheared dart rays. The
same positive denominator applies throughout one cell. This includes all six
actual shape affine maps, including the downward wire shear. -/
noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram IntegerStraightDrawing

def shearDenominator : ℤ := 1000000000000

def delta (s : CellShape) (e : LocalPatch.Edge s) : Point :=
  let a:=integerPoint s (fastSource s e)
  let b:=integerPoint s (fastTarget s e)
  (b.1-a.1,b.2-a.2)

def integerRay (s : CellShape) (a : Dart (LocalPatch.Edge s)) : Point :=
  let d:=delta s a.1
  let p:Point:=(shearDenominator*d.1+d.2,shearDenominator*d.2)
  if a.2 then p else (-p.1,-p.2)

def IntegerClockwise (p q : Point) : Prop :=
  (0<p.1*q.1 ∧ p.1*q.2-p.2*q.1<0) ∨ (0<p.1 ∧ q.1<0)

instance (p q : Point) : Decidable (IntegerClockwise p q) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

end PlanarHom.ColoringEmitter.MacroGeometry
