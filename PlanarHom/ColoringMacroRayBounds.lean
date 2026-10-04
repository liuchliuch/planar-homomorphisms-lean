import PlanarHom.ColoringMacroIntegerRays
import PlanarHom.ColoringMacroPlacedDrawing

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram IntegerStraightDrawing

theorem integerPoint_y_bound (s : CellShape) (v : LocalPatch.NumericVertex s) :
    -256000000<(integerPoint s v).2 ∧ (integerPoint s v).2<256000000 := by
  have h:=pointBound_all s v
  unfold PointBound bandLow bandHigh at h
  cases s <;> simp [width,CellShape.leftLo,CellShape.rightLo,CellShape.leftHi,CellShape.rightHi] at h
  all_goals omega

theorem delta_y_bound (s : CellShape) (e : LocalPatch.Edge s) :
    -shearDenominator<(delta s e).2 ∧ (delta s e).2<shearDenominator := by
  have ha:=integerPoint_y_bound s (fastSource s e)
  have hb:=integerPoint_y_bound s (fastTarget s e)
  change -1000000000000<_ ∧ _<1000000000000
  dsimp [delta]
  omega

theorem integerPoint_injective (D : RawDrawings) (s : CellShape) : Function.Injective (integerPoint s) := by
  intro v w h
  apply (normalizedDrawing D s).point_injective
  rw [normalizedDrawing_point,normalizedDrawing_point]
  simp only [normalizedPoint,h]

theorem numeric_endpoints_ne (s : CellShape) (e : LocalPatch.Edge s) :
    (LocalPatch.numericGraph s).src e≠(LocalPatch.numericGraph s).dst e := by
  let col := (MacroSemantics.partsEquiv s).colorings (MacroSemantics.witness s)
  exact fun h => col.property e (congrArg col.val h)

theorem delta_components_ne (D : RawDrawings) (s : CellShape) (e : LocalPatch.Edge s) :
    (delta s e).1≠0 ∨ (delta s e).2≠0 := by
  by_contra h
  push_neg at h
  have hp : integerPoint s (fastSource s e)=integerPoint s (fastTarget s e) := by
    apply Prod.ext
    · have hh:=h.1; dsimp [delta] at hh; omega
    · have hh:=h.2; dsimp [delta] at hh; omega
  have he:=integerPoint_injective D s hp
  rw [fastSource_eq,fastTarget_eq] at he
  exact numeric_endpoints_ne s e he

theorem sheared_integer_x_ne (D : RawDrawings) (s : CellShape) (a : Dart (LocalPatch.Edge s)) :
    (integerRay s a).1≠0 := by
  have hn:=delta_components_ne D s a.1
  have hb:=delta_y_bound s a.1
  dsimp [integerRay,shearDenominator]
  cases a.2 <;> simp only [Bool.false_eq_true,if_false,if_true,Prod.fst]
  all_goals dsimp [shearDenominator] at hb
  all_goals omega

theorem sheared_integer_x_pos (s : CellShape) (e : LocalPatch.Edge s) (h : 0<(delta s e).1) :
    0<(integerRay s (e,true)).1 := by
  have hb:=delta_y_bound s e
  dsimp [integerRay,shearDenominator] at *
  omega

theorem sheared_integer_x_neg (s : CellShape) (e : LocalPatch.Edge s) (h : (delta s e).1<0) :
    (integerRay s (e,true)).1<0 := by
  have hb:=delta_y_bound s e
  dsimp [integerRay,shearDenominator] at *
  omega

end PlanarHom.ColoringEmitter.MacroGeometry
