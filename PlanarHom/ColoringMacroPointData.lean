import PlanarHom.ColoringWireMacroCoordinates
import PlanarHom.ColoringCrossMacroCoordinates
import PlanarHom.ColoringFanMacroCoordinates
import PlanarHom.ColoringTestMacroCoordinates
import PlanarHom.ColoringEmitterLocalPatches
import PlanarHom.ColoringRailBands

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing

def width : CellShape → ℤ
  | .wireTop | .wireBottom | .wireDown | .fan => 64000000
  | .cross | .test => 64000

theorem width_pos (s : CellShape) : 0<width s := by cases s <;> decide

def basePoint (s : CellShape) : LocalPatch.NumericVertex s → Point :=
  match s with
  | .wireTop | .wireBottom | .wireDown => ColoringWireMacroCoordinates.point
  | .cross => ColoringCrossMacroCoordinates.point
  | .fan => ColoringFanMacroCoordinates.point
  | .test => ColoringTestMacroCoordinates.point

def adjust (s : CellShape) (p : Point) : Point :=
  match s with
  | .wireBottom => (p.1,p.2-width s)
  | .wireDown => (p.1,p.2-p.1)
  | _ => p

def integerPoint (s : CellShape) (v : LocalPatch.NumericVertex s) : Point := adjust s (basePoint s v)

def bandLow (s : CellShape) (p : Point) : ℤ :=
  width s*(s.leftLo:ℤ)+p.1*((s.rightLo:ℤ)-(s.leftLo:ℤ))-width s/4

def bandHigh (s : CellShape) (p : Point) : ℤ :=
  width s*(s.leftHi:ℤ)+p.1*((s.rightHi:ℤ)-(s.leftHi:ℤ))+width s/4

def PointBound (s : CellShape) (v : LocalPatch.NumericVertex s) : Prop :=
  let p:=integerPoint s v
  0≤p.1 ∧ p.1≤width s ∧ bandLow s p< -p.2 ∧ -p.2<bandHigh s p

instance (s : CellShape) (v : LocalPatch.NumericVertex s) : Decidable (PointBound s v) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def InteriorOrPort (s : CellShape) (v : LocalPatch.NumericVertex s) : Prop :=
  (0<(integerPoint s v).1 ∧ (integerPoint s v).1<width s) ∨ ∃p,LocalPatch.portVertex s p=v

instance (s : CellShape) (v : LocalPatch.NumericVertex s) : Decidable (InteriorOrPort s v) := inferInstanceAs (Decidable (_ ∨ _))

def EdgeInterior (s : CellShape) (e : LocalPatch.Edge s) : Prop :=
  let a:=integerPoint s ((LocalPatch.numericGraph s).src e)
  let b:=integerPoint s ((LocalPatch.numericGraph s).dst e)
  (0<a.1 ∨ 0<b.1) ∧ (a.1<width s ∨ b.1<width s)

instance (s : CellShape) (e : LocalPatch.Edge s) : Decidable (EdgeInterior s e) := inferInstanceAs (Decidable (_ ∧ _))

def originCell (s : CellShape) : Cell := ⟨0,0,s,0,(0,0,0)⟩

def PortCoordinate (s : CellShape) (p : LocalPatch.Port s) : Prop :=
  integerPoint s (LocalPatch.portVertex s p)=
    (width s*((originCell s).portData p.1).2.1,
     -width s*((originCell s).portData p.1).2.2+(width s/16)*p.2.val)

instance (s : CellShape) (p : LocalPatch.Port s) : Decidable (PortCoordinate s p) := inferInstanceAs (Decidable (_ = _))

theorem port_coordinates (s : CellShape) : ∀p,PortCoordinate s p := by cases s <;> decide +kernel

end PlanarHom.ColoringEmitter.MacroGeometry
