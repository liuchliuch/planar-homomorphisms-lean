import PlanarHom.ColoringCanvasShear
import PlanarHom.ColoringMacroRayBounds
import PlanarHom.RadialPottsAssemblyGeneralRows

noncomputable section
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram IntegerStraightDrawing
open RadialPottsAssemblyGeometry PlanarityLRRealization
namespace MacroGeometry

def rayScale (s : CellShape) : ℝ := 1/((shearDenominator:ℝ)*(width s:ℝ))
def ray (s : CellShape) (a : Dart (LocalPatch.Edge s)) : Plane := rayScale s • toPlane (integerRay s a)

theorem rayScale_pos (s : CellShape) : 0<rayScale s := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num [shearDenominator]) (width_real_pos s)

theorem ray_x_ne (D : RawDrawings) (s : CellShape) (a : Dart (LocalPatch.Edge s)) : (ray s a).1≠0 := by
  change rayScale s*((integerRay s a).1:ℝ)≠0
  exact mul_ne_zero (rayScale_pos s).ne' (by exact_mod_cast sheared_integer_x_ne D s a)

theorem integerClockwise_real (p q : Point) (h : IntegerClockwise p q) :
    ClockwiseRayOrder (toPlane p) (toPlane q) := by
  rcases h with ⟨hx,hc⟩ | ⟨hp,hq⟩
  · left
    constructor
    · change (0:ℝ)<(p.1:ℝ)*(q.1:ℝ)
      exact_mod_cast hx
    · change (p.1:ℝ)*q.2-(p.2:ℝ)*q.1<0
      exact_mod_cast hc
  · right
    change (0:ℝ)<(p.1:ℝ) ∧ (q.1:ℝ)<0
    exact ⟨by exact_mod_cast hp,by exact_mod_cast hq⟩

theorem ray_clockwise (s : CellShape) (a b : Dart (LocalPatch.Edge s))
    (h : IntegerClockwise (integerRay s a) (integerRay s b)) : ClockwiseRayOrder (ray s a) (ray s b) :=
  clockwiseRayOrder_smul _ _ (rayScale_pos s) (rayScale_pos s) (integerClockwise_real _ _ h)

theorem ray_formula (s : CellShape) (a : Dart (LocalPatch.Edge s)) : ray s a=
    if a.2 then
      Canvas.shear (normalizedPoint s (fastTarget s a.1))-Canvas.shear (normalizedPoint s (fastSource s a.1))
    else
      Canvas.shear (normalizedPoint s (fastSource s a.1))-Canvas.shear (normalizedPoint s (fastTarget s a.1)) := by
  have hw : (width s:ℝ)≠0 := (width_real_pos s).ne'
  obtain ⟨e,b⟩:=a
  cases b
  all_goals apply Prod.ext
  all_goals simp [ray,rayScale,toPlane,integerRay,delta,normalizedPoint,Canvas.shear,shearDenominator]
  all_goals field_simp
  all_goals ring

end MacroGeometry
namespace Canvas
open ParsimoniousNorOneInThree

def liftDart (f : NumericFormula) (i : Index f) (a : Dart (PatchEdge f i)) : Dart (Edge f) := (⟨i,a.1⟩,a.2)

theorem drawingFrom_point_place (D : MacroGeometry.RawDrawings) (f : NumericFormula)
    (i : Index f) (v : Port f i ⊕ Private f i) :
    (drawingFrom D f).point (PortPatchAssembly.placeVertex (port f) i v)=
      (MacroGeometry.placedDrawing D (canvasCell f i)).point v :=
  PortPatchAssembly.point_place (patch f) (fun i=>MacroGeometry.placedDrawing D (canvasCell f i))
    (point f) (port f) (fun i p=>MacroGeometry.placed_port D (canvasCell f i) p) i v

theorem sheared_endpointRay (D : MacroGeometry.RawDrawings) (f : NumericFormula)
    (i : Index f) (a : Dart (PatchEdge f i)) :
    (shearedDrawingFrom D f).endpointRay (liftDart f i a)=MacroGeometry.ray (canvasCell f i).shape a := by
  rw [MacroGeometry.ray_formula]
  obtain ⟨e,b⟩:=a
  cases b
  all_goals change (shear ((drawingFrom D f).point (PortPatchAssembly.placeVertex (port f) i _))) - (shear ((drawingFrom D f).point (PortPatchAssembly.placeVertex (port f) i _))) = _
  all_goals rw [drawingFrom_point_place,drawingFrom_point_place,MacroGeometry.placed_point,MacroGeometry.placed_point]
  all_goals simp only [liftDart,patch,LocalPatch.graph_source,LocalPatch.graph_target,MacroGeometry.fastSource_eq,MacroGeometry.fastTarget_eq]
  all_goals apply Prod.ext <;> simp [shear] <;> ring

theorem sheared_endpointRay_nonvertical (D : MacroGeometry.RawDrawings) (f : NumericFormula)
    (a : Dart (Edge f)) : ((shearedDrawingFrom D f).endpointRay a).1≠0 := by
  obtain ⟨⟨i,e⟩,b⟩:=a
  rw [show (⟨⟨i,e⟩,b⟩ : Dart (Edge f))=liftDart f i (e,b) from rfl,sheared_endpointRay]
  exact MacroGeometry.ray_x_ne D _ _

end Canvas
end PlanarHom.ColoringEmitter
