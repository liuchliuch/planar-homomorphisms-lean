import PlanarHom.PositiveRoutingCompiler

/-! Concrete macro-grid cells for the exact materialized routing compiler.
Every cell records its position, ordered port geometry, fresh-variable base,
and literal operands. Erasure is proved equal to the emitted block program. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree AdjacentRailRouting

inductive CellShape | wireTop | wireBottom | wireDown | cross | fan | test deriving DecidableEq, Fintype

def CellShape.kind : CellShape → Kind
  | .wireTop | .wireBottom | .wireDown => .wire
  | .cross => .cross
  | .fan => .fan
  | .test => .test

def CellShape.height : CellShape → ℕ
  | .test => 2
  | _ => 1

/-- Column c occupies x∈(64c,64(c+1)); row r is the top rail y=-64r.
All input and output ports lie on the integer-column boundaries. -/
structure Cell where
  column : ℕ
  row : ℕ
  shape : CellShape
  base : ℕ
  args : ℕ × ℕ × ℕ
  deriving DecidableEq

def Cell.instruction (c : Cell) : Instruction := (c.shape.kind,c.args)

def wireCells (shape : CellShape) (col row m : ℕ) : List ℕ → List Cell
  | [] => []
  | x::xs => ⟨col,row,shape,m,(x,0,0)⟩::wireCells shape col (row+1) (m+6) xs

def swapCells (col : ℕ) : ℕ → ℕ → ℕ → List ℕ → List Cell
  | row,m,0,a::b::rs =>
    ⟨col,row,.cross,m,(b,a,0)⟩::wireCells .wireBottom col (row+1) (m+15) rs
  | row,m,i+1,a::rs =>
    ⟨col,row,.wireTop,m,(a,0,0)⟩::swapCells col (row+1) (m+6) i rs
  | row,m,_,rs => wireCells .wireTop col row m rs

def copyCells (col : ℕ) : ℕ → ℕ → ℕ → List ℕ → List Cell
  | row,m,0,a::rs =>
    ⟨col,row,.fan,m,(a,0,0)⟩::wireCells .wireDown col (row+1) (m+12) rs
  | row,m,i+1,a::rs =>
    ⟨col,row,.wireTop,m,(a,0,0)⟩::copyCells col (row+1) (m+6) i rs
  | _,_,_,[] => []

def checkCells (col n m : ℕ) (rs : List ℕ) : List Cell :=
  wireCells .wireTop col 0 m (rs.take n)++
    [⟨col,n,.test,m+6*(rs.take n).length,(getRef rs n,getRef rs (n+1),getRef rs (n+2))⟩]

theorem wireCells_erase (shape : CellShape) (hshape : shape.kind=.wire) (col row m : ℕ) (rs : List ℕ) :
    (wireCells shape col row m rs).map Cell.instruction=wireProgram rs := by
  induction rs generalizing row m with
  | nil => rfl
  | cons a rs ih => simp [wireCells,Cell.instruction,hshape,wireProgram,wire,ih]

theorem swapCells_erase (col row m i : ℕ) (rs : List ℕ) :
    (swapCells col row m i rs).map Cell.instruction=(swapLayer m i rs).instructions := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      cases rs with
      | nil => exact wireCells_erase .wireTop rfl col row m [a]
      | cons b rs => simp [swapCells,swapLayer,passive,Cell.instruction,CellShape.kind,crossing,wireCells_erase]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs => simp [swapCells,swapLayer,Cell.instruction,CellShape.kind,wire,ih]

theorem copyCells_erase (col row m i : ℕ) (rs : List ℕ) :
    (copyCells col row m i rs).map Cell.instruction=(copyLayer m i rs).instructions := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs => simp [copyCells,copyLayer,passive,Cell.instruction,CellShape.kind,fan,wireCells_erase]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs => simp [copyCells,copyLayer,Cell.instruction,CellShape.kind,wire,ih]

theorem checkCells_erase (col n m : ℕ) (rs : List ℕ) :
    (checkCells col n m rs).map Cell.instruction=(checkLayer n m rs).instructions := by
  simp [checkCells,checkLayer,wireCells_erase,Cell.instruction,CellShape.kind,test]

def sweepCells (col m : ℕ) (rs : List ℕ) : List ℕ → List Cell
  | [] => []
  | i::is =>
    let first := swapLayer m i rs
    swapCells col 0 m i rs++sweepCells (col+1) first.variableCount first.rails is

theorem sweepCells_erase (is : List ℕ) (col m : ℕ) (rs : List ℕ) :
    (sweepCells col m rs is).map Cell.instruction=(sweep m rs is).instructions := by
  induction is generalizing col m rs with
  | nil => rfl
  | cons i is ih => simp [sweepCells,sweep,LayerResult.then,swapCells_erase,ih]

def copyColumns (n i : ℕ) : ℕ := if i<n then 2*(n-1-i)+1 else 0

def macroCells (col n i m : ℕ) (rs : List ℕ) : List Cell :=
  if i<n then
    let swaps := moveScript i (n-1-i)
    let first := sweep m rs swaps
    let second := copyLayer first.variableCount (n-1) first.rails
    sweepCells col m rs swaps++copyCells (col+swaps.length) 0 first.variableCount (n-1) first.rails++
      sweepCells (col+swaps.length+1) second.variableCount second.rails swaps.reverse
  else []

theorem macroCells_erase (col n i m : ℕ) (rs : List ℕ) :
    (macroCells col n i m rs).map Cell.instruction=(copyMacro n i m rs).instructions := by
  by_cases hi : i<n
  · simp [macroCells,copyMacro,hi,LayerResult.then,sweepCells_erase,copyCells_erase,List.append_assoc]
  · simp [macroCells,copyMacro,hi,LayerResult.identity]

def gatherColumns (n : ℕ) (is : List ℕ) : ℕ := (is.map (copyColumns n)).sum

def gatherCells (col n m : ℕ) (rs : List ℕ) : List ℕ → List Cell
  | [] => []
  | i::is =>
    let first := copyMacro n i m rs
    macroCells col n i m rs++gatherCells (col+copyColumns n i) n first.variableCount first.rails is

theorem gatherCells_erase (is : List ℕ) (col n m : ℕ) (rs : List ℕ) :
    (gatherCells col n m rs is).map Cell.instruction=(gatherMacro n m rs is).instructions := by
  induction is generalizing col m rs with
  | nil => rfl
  | cons i is ih => simp [gatherCells,gatherMacro,LayerResult.then,macroCells_erase,ih]

def clauseColumns (n : ℕ) (c : Clause ℕ) : ℕ := gatherColumns n [c.1,c.2.1,c.2.2]+1

def clauseCells (col n m : ℕ) (rs : List ℕ) (c : Clause ℕ) : List Cell :=
  let gathered := gatherClause n m rs c
  gatherCells col n m rs [c.1,c.2.1,c.2.2]++
    checkCells (col+gatherColumns n [c.1,c.2.1,c.2.2]) n gathered.variableCount gathered.rails

theorem clauseCells_erase (col n m : ℕ) (rs : List ℕ) (c : Clause ℕ) :
    (clauseCells col n m rs c).map Cell.instruction=(clauseLayer n m rs c).instructions := by
  simp [clauseCells,clauseLayer,LayerResult.then,gatherCells_erase,checkCells_erase,gatherClause]

def formulaColumns (n : ℕ) (f : Formula ℕ) : ℕ := (f.map (clauseColumns n)).sum

def formulaCells (col n m : ℕ) (rs : List ℕ) : Formula ℕ → List Cell
  | [] => []
  | c::cs =>
    let first := clauseLayer n m rs c
    clauseCells col n m rs c++formulaCells (col+clauseColumns n c) n first.variableCount first.rails cs

theorem formulaCells_erase (f : Formula ℕ) (col n m : ℕ) (rs : List ℕ) :
    (formulaCells col n m rs f).map Cell.instruction=(formulaLayers n m rs f).instructions := by
  induction f generalizing col m rs with
  | nil => rfl
  | cons c cs ih => simp [formulaCells,formulaLayers,LayerResult.then,clauseCells_erase,ih]

/-- The complete concrete cell trace of the already checked numeric compiler. -/
def canvas (f : NumericFormula) : List Cell := formulaCells 0 f.1 f.1 (List.range f.1) f.2

/-- A literal erasure identity, not just matching lengths or Boolean meaning. -/
theorem canvas_erase (f : NumericFormula) : (canvas f).map Cell.instruction=PositiveRoutingCompiler.program f :=
  formulaCells_erase _ _ _ _ _

/-- The grid width has an explicit linear-in-clauses bound. -/
theorem copyColumns_le (n i : ℕ) : copyColumns n i≤2*n+1 := by
  unfold copyColumns
  split <;> omega

theorem clauseColumns_le (n : ℕ) (c : Clause ℕ) : clauseColumns n c≤6*n+4 := by
  have h1 := copyColumns_le n c.1
  have h2 := copyColumns_le n c.2.1
  have h3 := copyColumns_le n c.2.2
  simp only [clauseColumns,gatherColumns,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem formulaColumns_le (n : ℕ) (f : Formula ℕ) : formulaColumns n f≤f.length*(6*n+4) := by
  induction f with
  | nil => simp [formulaColumns]
  | cons c cs ih =>
    have hc := clauseColumns_le n c
    simp only [formulaColumns,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    nlinarith

end PlanarHom.PositiveBlockProgram
