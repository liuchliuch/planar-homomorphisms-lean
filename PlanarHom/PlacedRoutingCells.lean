import PlanarHom.RoutingCellDrawings

/-! Translation of each concrete cell into its recorded macro-grid rectangle,
with exact signal-port locations and strict interior-region certificates. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.PositiveBlockProgram
open MultiGraph IntegerStraightDrawing ParsimoniousBlockTemplate

def translatePlane (offset : Plane) : C(Plane,Plane) where
  toFun p := (offset.1+p.1,offset.2+p.2)
  continuous_toFun := by fun_prop

theorem translatePlane_injective (offset : Plane) : Function.Injective (translatePlane offset) := by
  intro p q h
  apply Prod.ext
  · have hx := congrArg Prod.fst h; dsimp [translatePlane] at hx; linarith
  · have hy := congrArg Prod.snd h; dsimp [translatePlane] at hy; linarith

def mapDrawing {V E : Type} {G : MultiGraph V E} (d : PlaneDrawing G) (f : C(Plane,Plane))
    (hf : Function.Injective f) : PlaneDrawing G where
  point := f ∘ d.point
  point_injective := hf.comp d.point_injective
  curve e := f.comp (d.curve e)
  curve_zero e := congrArg f (d.curve_zero e)
  curve_one e := congrArg f (d.curve_one e)
  interior_injective e g s t hs ht h := d.interior_injective e g s t hs ht (hf h)
  interior_avoids e t ht v h := d.interior_avoids e t ht v (hf h)

def Cell.offset (c : Cell) : Plane := (64*(c.column:ℝ),-64*((c.row+c.shape.height:ℕ):ℝ))

def Cell.placedDrawing (c : Cell) : PlaneDrawing c.shape.kind.incidence :=
  mapDrawing c.shape.drawing (translatePlane c.offset) (translatePlane_injective c.offset)

def Cell.region (c : Cell) : Set Plane := {p |
  64*(c.column:ℝ)<p.1 ∧ p.1<64*((c.column:ℝ)+1) ∧
  -64*((c.row+c.shape.height:ℕ):ℝ)<p.2 ∧ p.2< -64*(c.row:ℝ)}

def gridPoint (col row : ℕ) : Plane := (64*(col:ℝ),-64*(row:ℝ))

/-- The points recorded in the trace are exactly the placed local-drawing ports. -/
theorem Cell.placed_port (c : Cell) (i : Fin c.shape.portCount) :
    c.placedDrawing.point (.inl (c.shape.portVertex i))=
      gridPoint (c.portData i).2.1 (c.portData i).2.2 := by
  change (c.offset.1+((c.shape.variablePoint (c.shape.portVertex i)).1:ℝ),
    c.offset.2+((c.shape.variablePoint (c.shape.portVertex i)).2:ℝ))=_
  rw [c.shape.port_points i]
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases i
  all_goals simp [Cell.offset,CellShape.portPoint,Cell.portData,CellShape.height,gridPoint,
    Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals first | (constructor <;> ring) | ring
  all_goals simp

/-- Every open edge interior lies in the actual rectangle assigned to its cell. -/
theorem Cell.curve_in_region (c : Cell) (e : Fin c.shape.kind.clauseCount × Fin 3) (t : I) (ht : Inside t) :
    c.placedDrawing.curve e t∈c.region := by
  have h := c.shape.curves_inside e t ht
  rcases h with ⟨hx0,hx1,hy0,hy1⟩
  change 64*(c.column:ℝ)<c.offset.1+(c.shape.drawing.curve e t).1 ∧
    c.offset.1+(c.shape.drawing.curve e t).1<64*((c.column:ℝ)+1) ∧
    -64*((c.row+c.shape.height:ℕ):ℝ)<c.offset.2+(c.shape.drawing.curve e t).2 ∧
    c.offset.2+(c.shape.drawing.curve e t).2< -64*(c.row:ℝ)
  dsimp [Cell.offset]
  push_cast
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

/-- Auxiliary variables and clause nodes are strictly in their own rectangle. -/
theorem Cell.auxiliary_in_region (c : Cell) (v : Fin c.shape.kind.variableCount)
    (hv : c.shape.portCount≤v.val) : c.placedDrawing.point (.inl v)∈c.region := by
  have h := c.shape.auxiliaries_inside v hv
  have h' : (0:ℝ)<(c.shape.variablePoint v).1 ∧ ((c.shape.variablePoint v).1:ℝ)<64 ∧
      (0:ℝ)<(c.shape.variablePoint v).2 ∧ ((c.shape.variablePoint v).2:ℝ)<64*(c.shape.height:ℝ) := by exact_mod_cast h
  rcases h' with ⟨hx0,hx1,hy0,hy1⟩
  change 64*(c.column:ℝ)<c.offset.1+((c.shape.variablePoint v).1:ℝ) ∧
    c.offset.1+((c.shape.variablePoint v).1:ℝ)<64*((c.column:ℝ)+1) ∧
    -64*((c.row+c.shape.height:ℕ):ℝ)<c.offset.2+((c.shape.variablePoint v).2:ℝ) ∧
    c.offset.2+((c.shape.variablePoint v).2:ℝ)< -64*(c.row:ℝ)
  dsimp [Cell.offset]
  push_cast
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

theorem Cell.clause_in_region (c : Cell) (v : Fin c.shape.kind.clauseCount) :
    c.placedDrawing.point (.inr v)∈c.region := by
  have h := c.shape.clauses_inside v
  have h' : (0:ℝ)<(c.shape.clausePoint v).1 ∧ ((c.shape.clausePoint v).1:ℝ)<64 ∧
      (0:ℝ)<(c.shape.clausePoint v).2 ∧ ((c.shape.clausePoint v).2:ℝ)<64*(c.shape.height:ℝ) := by exact_mod_cast h
  rcases h' with ⟨hx0,hx1,hy0,hy1⟩
  change 64*(c.column:ℝ)<c.offset.1+((c.shape.clausePoint v).1:ℝ) ∧
    c.offset.1+((c.shape.clausePoint v).1:ℝ)<64*((c.column:ℝ)+1) ∧
    -64*((c.row+c.shape.height:ℕ):ℝ)<c.offset.2+((c.shape.clausePoint v).2:ℝ) ∧
    c.offset.2+((c.shape.clausePoint v).2:ℝ)< -64*(c.row:ℝ)
  dsimp [Cell.offset]
  push_cast
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

/-- All signal ports on all integer-column grid lines avoid every open cell. -/
theorem Cell.gridPoint_outside (c : Cell) (col row : ℕ) : gridPoint col row∉c.region := by
  rintro ⟨hx0,hx1,_⟩
  dsimp [gridPoint] at hx0 hx1
  have h0 : c.column<col := by exact_mod_cast (show (c.column:ℝ)<col by linarith)
  have h1 : col<c.column+1 := by exact_mod_cast (show (col:ℝ)<(c.column:ℝ)+1 by linarith)
  omega

/-- The reference list in the emitted instruction has exactly these local
signal-variable names, including the fanout output reversal. -/
theorem Cell.port_reference (c : Cell) (i : Fin c.shape.portCount) :
    c.instruction.1.template.translate c.base (refs c.instruction) (c.shape.portVertex i)=
      (c.portData i).1 := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases i
  all_goals simp [Cell.instruction,CellShape.kind,Kind.template,Template.translate,
    CellShape.portVertex,Cell.portData,refs,equality,crossover,fanout,termination]

end PlanarHom.PositiveBlockProgram
