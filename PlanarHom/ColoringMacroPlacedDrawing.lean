import PlanarHom.ColoringMacroBandGeometry
import PlanarHom.ColoringEmitterMacroSemantics
import PlanarHom.ColoringEmitterCanvas
import PlanarHom.ColoringCanvasBandOrder

/-! Affine placement of the actual integer macros into the literal emitted
canvas. The only drawing input is a family of actual fixed-macro drawings,
with their recorded coordinates and straight edge paths. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing

structure RawDrawings where
  drawing : ∀s,PlaneDrawing (LocalPatch.numericGraph s)
  point : ∀s v,(drawing s).point v=toPlane (basePoint s v)
  straight : ∀s e t,(drawing s).curve e t=
    affine ((drawing s).point ((LocalPatch.numericGraph s).src e))
      ((drawing s).point ((LocalPatch.numericGraph s).dst e)) t

def normalize (s : CellShape) : C(Plane,Plane) where
  toFun p := match s with
    | .wireBottom => (p.1/(width s:ℝ),p.2/(width s:ℝ)-1)
    | .wireDown => (p.1/(width s:ℝ),(p.2-p.1)/(width s:ℝ))
    | _ => (p.1/(width s:ℝ),p.2/(width s:ℝ))
  continuous_toFun := by cases s <;> fun_prop

theorem normalize_injective (s : CellShape) : Function.Injective (normalize s) := by
  intro a b h
  have hx:=congrArg Prod.fst h
  have hy:=congrArg Prod.snd h
  cases s <;> apply Prod.ext
  all_goals dsimp [normalize,width] at hx hy ⊢
  all_goals linarith

theorem normalize_integer (s : CellShape) (v : LocalPatch.NumericVertex s) :
    normalize s (toPlane (basePoint s v))=normalizedPoint s v := by
  cases s <;> apply Prod.ext
  all_goals simp [normalize,normalizedPoint,integerPoint,adjust,toPlane,width]
  all_goals ring

theorem normalize_affine (s : CellShape) (a b : Plane) (t : ℝ) :
    normalize s (affine a b t)=affine (normalize s a) (normalize s b) t := by
  cases s <;> apply Prod.ext <;> dsimp [normalize,affine,width] <;> ring

def normalizedDrawing (D : RawDrawings) (s : CellShape) : PlaneDrawing (LocalPatch.numericGraph s) :=
  mapDrawing (D.drawing s) (normalize s) (normalize_injective s)

theorem normalizedDrawing_point (D : RawDrawings) (s : CellShape) (v : LocalPatch.NumericVertex s) :
    (normalizedDrawing D s).point v=normalizedPoint s v := by
  change normalize s ((D.drawing s).point v)=_
  rw [D.point,normalize_integer]

theorem normalizedDrawing_curve (D : RawDrawings) (s : CellShape) (e : LocalPatch.Edge s) (t : I) :
    (normalizedDrawing D s).curve e t=affine
      (normalizedPoint s ((LocalPatch.numericGraph s).src e))
      (normalizedPoint s ((LocalPatch.numericGraph s).dst e)) t := by
  change normalize s ((D.drawing s).curve e t)=_
  rw [D.straight,normalize_affine,D.point,D.point,normalize_integer,normalize_integer]

def patchDrawing (D : RawDrawings) (s : CellShape) : PlaneDrawing (LocalPatch.graph s) :=
  (normalizedDrawing D s).transport (MacroSemantics.partsEquiv s).symm

def placedDrawing (D : RawDrawings) (c : Cell) : PlaneDrawing (LocalPatch.graph c.shape) :=
  mapDrawing (patchDrawing D c.shape) (translatePlane ((c.column:ℝ),-(c.row:ℝ)))
    (translatePlane_injective _)

theorem placed_point (D : RawDrawings) (c : Cell) (v : LocalPatch.Port c.shape ⊕ LocalPatch.Private c.shape) :
    (placedDrawing D c).point v=
      ((c.column:ℝ)+(normalizedPoint c.shape (LocalPatch.localVertexParts c.shape v)).1,
       -(c.row:ℝ)+(normalizedPoint c.shape (LocalPatch.localVertexParts c.shape v)).2) := by
  change translatePlane _ ((normalizedDrawing D c.shape).point (LocalPatch.localVertexParts c.shape v))=_
  rw [normalizedDrawing_point]
  rfl

theorem translated_in_band (c : Cell) (p : Plane)
    (h : 0<p.1 ∧ p.1<1 ∧ low c.shape p.1< -p.2 ∧ -p.2<high c.shape p.1) :
    ((c.column:ℝ)+p.1,-(c.row:ℝ)+p.2)∈c.colorBand := by
  rcases h with ⟨h0,h1,hl,hh⟩
  change (c.column:ℝ)<(c.column:ℝ)+p.1 ∧ (c.column:ℝ)+p.1<(c.column:ℝ)+1 ∧ _
  dsimp [low,high] at hl hh
  refine ⟨by linarith,by linarith,?_,?_⟩
  · dsimp
    nlinarith
  · dsimp
    nlinarith

theorem placed_private (D : RawDrawings) (c : Cell) (v : LocalPatch.Private c.shape) :
    (placedDrawing D c).point (.inr v)∈c.colorBand := by
  rw [placed_point,LocalPatch.localVertexParts_private]
  have h:=normalized_bound c.shape v.val
  have hx:=private_horizontal c.shape v
  exact translated_in_band c _ ⟨hx.1,hx.2,h.2.2.1,h.2.2.2⟩

theorem placed_curve (D : RawDrawings) (c : Cell) (e : LocalPatch.Edge c.shape) (t : I) (ht : Inside t) :
    (placedDrawing D c).curve e t∈c.colorBand := by
  change translatePlane _ ((normalizedDrawing D c.shape).curve e t)∈_
  rw [normalizedDrawing_curve]
  exact translated_in_band c _ (affine_inside c.shape e t ht)

theorem normalized_port (s : CellShape) (p : LocalPatch.Port s) :
    normalizedPoint s (LocalPatch.portVertex s p)=
      ((((originCell s).portData p.1).2.1:ℝ),-(((originCell s).portData p.1).2.2:ℝ)+(p.2.val:ℝ)/16) := by
  have hp:=port_coordinates s p
  unfold PortCoordinate at hp
  simp only [normalizedPoint,hp]
  have hw : (width s:ℝ)≠0:=(width_real_pos s).ne'
  have h16 : ((width s/16:ℤ):ℝ)=(width s:ℝ)/16 := by cases s <;> norm_num [width]
  push_cast
  rw [h16]
  apply Prod.ext <;> dsimp <;> field_simp <;> ring

theorem placed_port (D : RawDrawings) (c : Cell) (p : LocalPatch.Port c.shape) :
    (placedDrawing D c).point (.inl p)=colorBoundaryPoint (c.portData p.1).2 p.2 := by
  rw [placed_point,LocalPatch.localVertexParts_port,normalized_port]
  obtain ⟨p,k⟩:=p
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases p
  all_goals simp [Cell.portData,originCell,colorBoundaryPoint]
  all_goals first | (apply Prod.ext <;> dsimp <;> ring) | ring

end PlanarHom.ColoringEmitter.MacroGeometry
