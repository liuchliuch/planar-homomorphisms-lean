import PlanarHom.RoutingCellPorts

/-! Actual fixed drawings for every kind of routing cell, in the exact port
orders recorded by the materialized trace. Wires include their local grounds;
termination is a height-two three-input star. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.PositiveBlockProgram
open MultiGraph ParsimoniousNorOneInThree ParsimoniousBlockTemplate IntegerStraightDrawing
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def Kind.variableCount (k : Kind) : ℕ := k.template.inputs+k.template.fresh

def Kind.clauseCount : Kind → ℕ
  | .wire => 5
  | .cross => 12
  | .fan => 10
  | .test => 1

def Kind.clauseData (k : Kind) : Fin k.clauseCount → Clause (Fin k.variableCount) :=
  match k with
  | .wire => PositiveEqualityDrawing.clauses
  | .cross => PositiveCrossoverDrawing.clauses
  | .fan => PositiveFanoutDrawing.clauses
  | .test => fun _ => ((0 : Fin 3),(1 : Fin 3),(2 : Fin 3))

theorem Kind.clauses_eq (k : Kind) : k.template.clauses=List.ofFn k.clauseData := by
  cases k
  · rfl
  · rfl
  · exact PositiveFanoutDrawing.formula_eq
  · rfl

def Kind.occurrence (k : Kind) (c : Fin k.clauseCount) : Fin 3 → Fin k.variableCount :=
  ![(k.clauseData c).1,(k.clauseData c).2.1,(k.clauseData c).2.2]

def Kind.incidence (k : Kind) : MultiGraph (Fin k.variableCount ⊕ Fin k.clauseCount) (Fin k.clauseCount × Fin 3) where
  src e := .inl (k.occurrence e.1 e.2)
  dst e := .inr e.1

def CellShape.variablePoint (s : CellShape) : Fin s.kind.variableCount → Point :=
  match s with
  | .wireTop => fun i => let p := PositiveEqualityDrawing.variablePoint i; (4*p.1,64-p.2)
  | .wireBottom => fun i => let p := PositiveEqualityDrawing.variablePoint i; (4*p.1,p.2)
  | .wireDown => fun i => let p := PositiveEqualityDrawing.variablePoint i; (4*p.1,64-4*p.1-p.2)
  | .cross => fun i => let p := PositiveCrossoverDrawing.variablePoint i; (4*p.1,4*p.2)
  | .fan => fun i => let p := PositiveFanoutDrawing.variablePoint i; (p.1,64-p.2)
  | .test => ![(0,128),(0,64),(0,0)]

def CellShape.clausePoint (s : CellShape) : Fin s.kind.clauseCount → Point :=
  match s with
  | .wireTop => fun i => let p := PositiveEqualityDrawing.clausePoint i; (4*p.1,64-p.2)
  | .wireBottom => fun i => let p := PositiveEqualityDrawing.clausePoint i; (4*p.1,p.2)
  | .wireDown => fun i => let p := PositiveEqualityDrawing.clausePoint i; (4*p.1,64-4*p.1-p.2)
  | .cross => fun i => let p := PositiveCrossoverDrawing.clausePoint i; (4*p.1,4*p.2)
  | .fan => fun i => let p := PositiveFanoutDrawing.clausePoint i; (p.1,64-p.2)
  | .test => fun _ => (32,64)

def CellShape.point (s : CellShape) : Fin s.kind.variableCount ⊕ Fin s.kind.clauseCount → Point :=
  Sum.elim s.variablePoint s.clausePoint

/-- Every variant is independently checked over exact integer coordinates. -/
def CellShape.certificate (s : CellShape) : Certificate s.kind.incidence s.point := by
  cases s <;> exact {
    injective := by decide
    nondegenerate := by decide
    separated := by decide
    avoids := by decide }

def CellShape.drawing (s : CellShape) : PlaneDrawing s.kind.incidence :=
  IntegerStraightDrawing.drawing s.certificate

theorem CellShape.portCount_le (s : CellShape) : s.portCount≤s.kind.variableCount := by cases s <;> decide

def CellShape.portVertex (s : CellShape) (i : Fin s.portCount) : Fin s.kind.variableCount :=
  ⟨i.val,lt_of_lt_of_le i.isLt s.portCount_le⟩

def CellShape.portPoint (s : CellShape) : Fin s.portCount → Point :=
  match s with
  | .wireTop => ![(0,64),(64,64)]
  | .wireBottom => ![(0,0),(64,0)]
  | .wireDown => ![(0,64),(64,0)]
  | .cross => ![(0,0),(0,64),(64,64),(64,0)]
  | .fan => ![(0,64),(64,0),(64,64)]
  | .test => ![(0,128),(0,64),(0,0)]

theorem CellShape.port_points (s : CellShape) : ∀ i,s.variablePoint (s.portVertex i)=s.portPoint i := by
  cases s <;> decide

theorem CellShape.variables_closed (s : CellShape) : ∀ v,
    0≤(s.variablePoint v).1 ∧ (s.variablePoint v).1≤64 ∧
    0≤(s.variablePoint v).2 ∧ (s.variablePoint v).2≤64*(s.height:ℤ) := by
  cases s <;> decide

theorem CellShape.clauses_inside (s : CellShape) : ∀ v,
    0<(s.clausePoint v).1 ∧ (s.clausePoint v).1<64 ∧
    0<(s.clausePoint v).2 ∧ (s.clausePoint v).2<64*(s.height:ℤ) := by
  cases s <;> decide

theorem CellShape.auxiliaries_inside (s : CellShape) : ∀ v,s.portCount≤v.val →
    0<(s.variablePoint v).1 ∧ (s.variablePoint v).1<64 ∧
    0<(s.variablePoint v).2 ∧ (s.variablePoint v).2<64*(s.height:ℤ) := by
  cases s <;> decide

private theorem blend_inside (a b M t : ℝ) (ha0 : 0≤a) (ha1 : a≤M)
    (hb0 : 0<b) (hb1 : b<M) (ht0 : 0<t) (ht1 : t<1) :
    0<(1-t)*a+t*b ∧ (1-t)*a+t*b<M := by
  constructor
  · nlinarith [mul_nonneg (show 0≤1-t by linarith) ha0,mul_pos ht0 hb0]
  · nlinarith [mul_nonneg (show 0≤1-t by linarith) (show 0≤M-a by linarith),
      mul_pos ht0 (show 0<M-b by linarith)]

/-- Every actual edge interior is strictly in its placement rectangle. -/
theorem CellShape.curves_inside (s : CellShape) (e : Fin s.kind.clauseCount × Fin 3)
    (t : I) (ht : Inside t) :
    0<(s.drawing.curve e t).1 ∧ (s.drawing.curve e t).1<64 ∧
    0<(s.drawing.curve e t).2 ∧ (s.drawing.curve e t).2<64*(s.height:ℝ) := by
  have hs := s.variables_closed (s.kind.occurrence e.1 e.2)
  have hd := s.clauses_inside e.1
  have hs' : (0:ℝ)≤(s.variablePoint (s.kind.occurrence e.1 e.2)).1 ∧
      ((s.variablePoint (s.kind.occurrence e.1 e.2)).1:ℝ)≤64 ∧
      (0:ℝ)≤(s.variablePoint (s.kind.occurrence e.1 e.2)).2 ∧
      ((s.variablePoint (s.kind.occurrence e.1 e.2)).2:ℝ)≤64*(s.height:ℝ) := by exact_mod_cast hs
  have hd' : (0:ℝ)<(s.clausePoint e.1).1 ∧ ((s.clausePoint e.1).1:ℝ)<64 ∧
      (0:ℝ)<(s.clausePoint e.1).2 ∧ ((s.clausePoint e.1).2:ℝ)<64*(s.height:ℝ) := by exact_mod_cast hd
  exact ⟨(blend_inside _ _ 64 t hs'.1 hs'.2.1 hd'.1 hd'.2.1 ht.1 ht.2).1,
    (blend_inside _ _ 64 t hs'.1 hs'.2.1 hd'.1 hd'.2.1 ht.1 ht.2).2,
    (blend_inside _ _ _ t hs'.2.2.1 hs'.2.2.2 hd'.2.2.1 hd'.2.2.2 ht.1 ht.2).1,
    (blend_inside _ _ _ t hs'.2.2.1 hs'.2.2.2 hd'.2.2.1 hd'.2.2.2 ht.1 ht.2).2⟩

end PlanarHom.PositiveBlockProgram
