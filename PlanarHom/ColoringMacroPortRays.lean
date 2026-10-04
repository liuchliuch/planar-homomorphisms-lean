import PlanarHom.ColoringCanvasDartRays
import PlanarHom.RotationRowsTransport
import PlanarHom.ColoringCanvasSharedPortOrder

noncomputable section
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram IntegerStraightDrawing

theorem port_integer_x (s : CellShape) (p : LocalPatch.Port s) :
    (integerPoint s (LocalPatch.portVertex s p)).1=width s*((originCell s).portData p.1).2.1 :=
  congrArg Prod.fst (port_coordinates s p)

theorem ray_left_port (s : CellShape) (a : Dart (LocalPatch.Edge s)) (p : LocalPatch.Port s)
    (hhost : ((LocalPatch.numericGraph s).dartPair a).1=LocalPatch.portVertex s p)
    (hleft : ((originCell s).portData p.1).2.1=0) : 0<(ray s a).1 := by
  have hp : (integerPoint s (LocalPatch.portVertex s p)).1=0 := by simpa [hleft] using port_integer_x s p
  obtain ⟨e,b⟩:=a
  have hi:=edgeInterior_all s e
  unfold EdgeInterior at hi
  rw [←fastSource_eq,←fastTarget_eq] at hi
  have hpos : 0<(integerRay s (e,b)).1 := by
    cases b
    · change (LocalPatch.numericGraph s).dst e=LocalPatch.portVertex s p at hhost
      have hh : (integerPoint s (fastTarget s e)).1=0 := by rw [fastTarget_eq,hhost,hp]
      have hd : (delta s e).1<0 := by dsimp [delta]; omega
      have hn:=sheared_integer_x_neg s e hd
      change 0< -(integerRay s (e,true)).1
      omega
    · change (LocalPatch.numericGraph s).src e=LocalPatch.portVertex s p at hhost
      have hh : (integerPoint s (fastSource s e)).1=0 := by rw [fastSource_eq,hhost,hp]
      have hd : 0<(delta s e).1 := by dsimp [delta]; omega
      exact sheared_integer_x_pos s e hd
  change 0<rayScale s*((integerRay s (e,b)).1:ℝ)
  exact mul_pos (rayScale_pos s) (by exact_mod_cast hpos)

theorem ray_right_port (s : CellShape) (a : Dart (LocalPatch.Edge s)) (p : LocalPatch.Port s)
    (hhost : ((LocalPatch.numericGraph s).dartPair a).1=LocalPatch.portVertex s p)
    (hright : ((originCell s).portData p.1).2.1=1) : (ray s a).1<0 := by
  have hp : (integerPoint s (LocalPatch.portVertex s p)).1=width s := by simpa [hright] using port_integer_x s p
  obtain ⟨e,b⟩:=a
  have hi:=edgeInterior_all s e
  unfold EdgeInterior at hi
  rw [←fastSource_eq,←fastTarget_eq] at hi
  have hneg : (integerRay s (e,b)).1<0 := by
    cases b
    · change (LocalPatch.numericGraph s).dst e=LocalPatch.portVertex s p at hhost
      have hh : (integerPoint s (fastTarget s e)).1=width s := by rw [fastTarget_eq,hhost,hp]
      have hd : 0<(delta s e).1 := by dsimp [delta]; omega
      have hn:=sheared_integer_x_pos s e hd
      change -(integerRay s (e,true)).1<0
      omega
    · change (LocalPatch.numericGraph s).src e=LocalPatch.portVertex s p at hhost
      have hh : (integerPoint s (fastSource s e)).1=width s := by rw [fastSource_eq,hhost,hp]
      have hd : (delta s e).1<0 := by dsimp [delta]; omega
      exact sheared_integer_x_neg s e hd
  change rayScale s*((integerRay s (e,b)).1:ℝ)<0
  exact mul_neg_of_pos_of_neg (rayScale_pos s) (by exact_mod_cast hneg)

theorem numeric_host_of_patch_port (s : CellShape) (a : Dart (LocalPatch.Edge s)) (p : LocalPatch.Port s)
    (h : ((LocalPatch.graph s).dartPair a).1=.inl p) :
    ((LocalPatch.numericGraph s).dartPair a).1=LocalPatch.portVertex s p := by
  exact ((MacroSemantics.partsEquiv s).dart_host a).trans (congrArg (LocalPatch.localVertexParts s) h)

theorem port_column_offset (c : Cell) (p : Fin c.shape.portCount) :
    (c.portData p).2.1=c.column+((originCell c.shape).portData p).2.1 := by
  rcases c with ⟨col,row,s,base,args⟩
  cases s <;> fin_cases p <;> simp [Cell.portData,originCell]

end PlanarHom.ColoringEmitter.MacroGeometry
