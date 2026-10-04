import PlanarHom.SignedNandCellDrawings

/-! The exact signed-NAND cells occupy the already certified disjoint routing
rectangles and share precisely the recorded signal ports. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.SignedNandCells
open MultiGraph PositiveBlockProgram ParsimoniousNorOneInThree IntegerStraightDrawing

def placedDrawing (c : Cell) : PlaneDrawing (graph c.shape.kind) :=
  mapDrawing (drawing c.shape) (translatePlane c.offset) (translatePlane_injective c.offset)

theorem translated_in_region (c : Cell) (p : Plane) (hp : p∈realBox (64*c.shape.height)) :
    translatePlane c.offset p∈c.region := by
  rcases hp with ⟨hx0,hx1,hy0,hy1⟩
  change 64*(c.column:ℝ)<c.offset.1+p.1 ∧ c.offset.1+p.1<64*((c.column:ℝ)+1) ∧
    -64*((c.row+c.shape.height:ℕ):ℝ)<c.offset.2+p.2 ∧ c.offset.2+p.2< -64*(c.row:ℝ)
  dsimp [Cell.offset]
  push_cast at hy1 ⊢
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

theorem placed_port (c : Cell) (i : Fin c.shape.portCount) :
    (placedDrawing c).point (.inl (c.shape.portVertex i))=gridPoint (c.portData i).2.1 (c.portData i).2.2 := by
  change translatePlane c.offset ((drawing c.shape).point (.inl (c.shape.portVertex i)))=_
  rw [drawing_point,port_points]
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases i
  all_goals simp [translatePlane,toPlane,Cell.offset,CellShape.portPoint,Cell.portData,CellShape.height,gridPoint,
    Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals first | (constructor <;> ring) | ring
  all_goals simp

theorem placed_curve_inside (c : Cell) (e : Fin (edgeCount c.shape.kind)) (t : I) (ht : Inside t) :
    (placedDrawing c).curve e t∈c.region := translated_in_region c _ (curves_inside c.shape e t ht)

def patchGraph (s : CellShape) : MultiGraph (Fin s.portCount ⊕ s.Internal) (Fin (edgeCount s.kind)) where
  src e := s.vertexEquiv.symm ((graph s.kind).src e)
  dst e := s.vertexEquiv.symm ((graph s.kind).dst e)

def patchDrawing (c : Cell) : PlaneDrawing (patchGraph c.shape) where
  point := (placedDrawing c).point ∘ c.shape.vertexEquiv
  point_injective := (placedDrawing c).point_injective.comp c.shape.vertexEquiv.injective
  curve := (placedDrawing c).curve
  curve_zero e := by simp [patchGraph,(placedDrawing c).curve_zero]
  curve_one e := by simp [patchGraph,(placedDrawing c).curve_one]
  interior_injective := (placedDrawing c).interior_injective
  interior_avoids e t ht v := (placedDrawing c).interior_avoids e t ht (c.shape.vertexEquiv v)

theorem patch_port (c : Cell) (i : Fin c.shape.portCount) :
    (patchDrawing c).point (.inl i)=gridPoint (c.portData i).2.1 (c.portData i).2.2 := by
  simp only [patchDrawing,Function.comp_apply,CellShape.vertexEquiv_port]
  exact placed_port c i

theorem patch_internal (c : Cell) (v : c.shape.Internal) : (patchDrawing c).point (.inr v)∈c.region := by
  cases v with
  | inl v =>
    simp only [patchDrawing,Function.comp_apply,CellShape.vertexEquiv_auxiliary]
    apply translated_in_region
    rw [drawing_point]
    exact openBox_cast (auxiliaries_inside c.shape _ (by simp))
  | inr v =>
    simp only [patchDrawing,Function.comp_apply,CellShape.vertexEquiv_clause]
    apply translated_in_region
    rw [drawing_point]
    exact openBox_cast (centers_inside c.shape v)

abbrev CanvasEdge (f : NumericFormula) (i : CanvasIndex f) := Fin (edgeCount (canvasCell f i).shape.kind)

def canvasGraph (f : NumericFormula) : MultiGraph (GridVertex f) ((i : CanvasIndex f) × CanvasEdge f i) :=
  PortPatchAssembly.graph (fun i => patchGraph (canvasCell f i).shape) (boundaryPort f)

/-- Every signed edge is an actual curve inside its own cell rectangle. Unary
marks add no edges, and no geometric bend is counted as a graph vertex. -/
def canvasDrawing (f : NumericFormula) : PlaneDrawing (canvasGraph f) := by
  apply PortPatchAssembly.drawing
    (fun i : CanvasIndex f => patchGraph (canvasCell f i).shape)
    (fun i => patchDrawing (canvasCell f i)) (fun i => (canvasCell f i).region)
    (boundaryPoint f) (boundaryPort f)
  · exact canvas_regions_disjoint f
  · exact boundaryPoint_injective f
  · intro i b; exact (canvasCell f i).gridPoint_outside b.val.1 b.val.2
  · intro i v; exact patch_internal (canvasCell f i) v
  · intro i e t ht; exact placed_curve_inside (canvasCell f i) e t ht
  · intro i k; exact patch_port (canvasCell f i) k

end PlanarHom.SignedNandCells
