import PlanarHom.RoutingCodeBounds

/-! A single explicit stage list for the routed formula. This exposes each
successive boundary frame for port-name/location coherence and machine folds. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree AdjacentRailRouting

inductive Stage | swap (index : ℕ) | copy (index : ℕ) | check (originals : ℕ) deriving DecidableEq

def Stage.render (s : Stage) (m : ℕ) (rs : List ℕ) : LayerResult :=
  match s with
  | .swap i => swapLayer m i rs
  | .copy i => copyLayer m i rs
  | .check n => checkLayer n m rs

def Stage.cells (s : Stage) (col m : ℕ) (rs : List ℕ) : List Cell :=
  match s with
  | .swap i => swapCells col 0 m i rs
  | .copy i => copyCells col 0 m i rs
  | .check n => checkCells col n m rs

def stages (m : ℕ) (rs : List ℕ) : List Stage → LayerResult
  | [] => .identity m rs
  | s::ss =>
    let first := s.render m rs
    first.then (stages first.variableCount first.rails ss)

def stagesCells (col m : ℕ) (rs : List ℕ) : List Stage → List Cell
  | [] => []
  | s::ss =>
    let first := s.render m rs
    s.cells col m rs++stagesCells (col+1) first.variableCount first.rails ss

def frames (m : ℕ) (rs : List ℕ) : List Stage → List (ℕ × List ℕ)
  | [] => [(m,rs)]
  | s::ss => (m,rs)::frames (s.render m rs).variableCount (s.render m rs).rails ss

@[simp] theorem frames_length (m : ℕ) (rs : List ℕ) (ss : List Stage) : (frames m rs ss).length=ss.length+1 := by
  induction ss generalizing m rs with
  | nil => rfl
  | cons s ss ih => simp [frames,ih]

theorem LayerResult.then_assoc (a b c : LayerResult) : (a.then b).then c=a.then (b.then c) := by
  cases a; cases b; cases c
  simp [LayerResult.then,List.append_assoc]

@[simp] theorem stages_append (ss ts : List Stage) (m : ℕ) (rs : List ℕ) :
    stages m rs (ss++ts)=(stages m rs ss).then (stages (stages m rs ss).variableCount (stages m rs ss).rails ts) := by
  induction ss generalizing m rs with
  | nil => simp [stages,LayerResult.identity,LayerResult.then]
  | cons s ss ih =>
    simp only [List.cons_append,stages,ih,LayerResult.then_assoc]
    rfl

@[simp] theorem stagesCells_append (ss ts : List Stage) (col m : ℕ) (rs : List ℕ) :
    stagesCells col m rs (ss++ts)=stagesCells col m rs ss++
      stagesCells (col+ss.length) (stages m rs ss).variableCount (stages m rs ss).rails ts := by
  induction ss generalizing col m rs with
  | nil => simp [stagesCells,stages,LayerResult.identity]
  | cons s ss ih =>
    simp only [List.cons_append,stagesCells,ih,stages,LayerResult.then,List.length_cons,List.append_assoc]
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

@[simp] theorem stages_swap_map (is : List ℕ) (m : ℕ) (rs : List ℕ) :
    stages m rs (is.map Stage.swap)=sweep m rs is := by
  induction is generalizing m rs with
  | nil => rfl
  | cons i is ih => simp [stages,sweep,Stage.render,ih]

@[simp] theorem stagesCells_swap_map (is : List ℕ) (col m : ℕ) (rs : List ℕ) :
    stagesCells col m rs (is.map Stage.swap)=sweepCells col m rs is := by
  induction is generalizing col m rs with
  | nil => rfl
  | cons i is ih => simp [stagesCells,sweepCells,Stage.render,Stage.cells,ih]

@[simp] theorem stages_reverse_swap_map (is : List ℕ) (m : ℕ) (rs : List ℕ) :
    stages m rs (is.map Stage.swap).reverse=sweep m rs is.reverse := by
  rw [←List.map_reverse,stages_swap_map]

@[simp] theorem stagesCells_reverse_swap_map (is : List ℕ) (col m : ℕ) (rs : List ℕ) :
    stagesCells col m rs (is.map Stage.swap).reverse=sweepCells col m rs is.reverse := by
  rw [←List.map_reverse,stagesCells_swap_map]

def copyStages (n i : ℕ) : List Stage :=
  if i<n then
    let is := moveScript i (n-1-i)
    is.map .swap++[.copy (n-1)]++is.reverse.map .swap
  else []

@[simp] theorem copyStages_length (n i : ℕ) : (copyStages n i).length=copyColumns n i := by
  by_cases h : i<n <;> simp [copyStages,copyColumns,h] <;> omega

@[simp] theorem stages_copyStages (n i m : ℕ) (rs : List ℕ) : stages m rs (copyStages n i)=copyMacro n i m rs := by
  by_cases h : i<n
  · simp [copyStages,copyMacro,h,stages_append,stages,Stage.render,LayerResult.then,List.append_assoc]
  · simp [copyStages,copyMacro,h,stages]

@[simp] theorem stagesCells_copyStages (col n i m : ℕ) (rs : List ℕ) :
    stagesCells col m rs (copyStages n i)=macroCells col n i m rs := by
  by_cases h : i<n
  · simp [copyStages,macroCells,h,stagesCells_append,stages,stagesCells,Stage.render,Stage.cells,
      LayerResult.then,List.append_assoc,Nat.add_assoc]
  · simp [copyStages,macroCells,h,stagesCells]

def gatherStages (n : ℕ) (is : List ℕ) : List Stage := is.flatMap (copyStages n)

@[simp] theorem gatherStages_length (n : ℕ) (is : List ℕ) : (gatherStages n is).length=gatherColumns n is := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [gatherStages,gatherColumns,ih]

@[simp] theorem stages_gatherStages (is : List ℕ) (n m : ℕ) (rs : List ℕ) :
    stages m rs (gatherStages n is)=gatherMacro n m rs is := by
  induction is generalizing m rs with
  | nil => rfl
  | cons i is ih =>
    simp only [gatherStages,List.flatMap_cons,stages_append,stages_copyStages,gatherMacro]
    exact congrArg _ (ih _ _)

@[simp] theorem stagesCells_gatherStages (is : List ℕ) (col n m : ℕ) (rs : List ℕ) :
    stagesCells col m rs (gatherStages n is)=gatherCells col n m rs is := by
  induction is generalizing col m rs with
  | nil => rfl
  | cons i is ih =>
    simp only [gatherStages,List.flatMap_cons,stagesCells_append,stagesCells_copyStages,
      copyStages_length,stages_copyStages,gatherCells]
    exact congrArg _ (ih _ _ _)

def clauseStages (n : ℕ) (c : Clause ℕ) : List Stage := gatherStages n [c.1,c.2.1,c.2.2]++[.check n]

@[simp] theorem clauseStages_length (n : ℕ) (c : Clause ℕ) : (clauseStages n c).length=clauseColumns n c := by
  simp [clauseStages,clauseColumns]

@[simp] theorem stages_clauseStages (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) :
    stages m rs (clauseStages n c)=clauseLayer n m rs c := by
  simp [clauseStages,clauseLayer,stages_append,stages,Stage.render,gatherClause,LayerResult.then,LayerResult.identity]

@[simp] theorem stagesCells_clauseStages (col n m : ℕ) (rs : List ℕ) (c : Clause ℕ) :
    stagesCells col m rs (clauseStages n c)=clauseCells col n m rs c := by
  simp [clauseStages,clauseCells,stagesCells_append,stagesCells,Stage.cells,gatherClause]

def formulaStages (n : ℕ) (f : Formula ℕ) : List Stage := f.flatMap (clauseStages n)

@[simp] theorem formulaStages_length (n : ℕ) (f : Formula ℕ) : (formulaStages n f).length=formulaColumns n f := by
  induction f with
  | nil => rfl
  | cons c cs ih => simp [formulaStages,formulaColumns,ih]

@[simp] theorem stages_formulaStages (f : Formula ℕ) (n m : ℕ) (rs : List ℕ) :
    stages m rs (formulaStages n f)=formulaLayers n m rs f := by
  induction f generalizing m rs with
  | nil => rfl
  | cons c cs ih =>
    simp only [formulaStages,List.flatMap_cons,stages_append,stages_clauseStages,formulaLayers]
    exact congrArg _ (ih _ _)

@[simp] theorem stagesCells_formulaStages (f : Formula ℕ) (col n m : ℕ) (rs : List ℕ) :
    stagesCells col m rs (formulaStages n f)=formulaCells col n m rs f := by
  induction f generalizing col m rs with
  | nil => rfl
  | cons c cs ih =>
    simp only [formulaStages,List.flatMap_cons,stagesCells_append,stagesCells_clauseStages,
      clauseStages_length,stages_clauseStages,formulaCells]
    exact congrArg _ (ih _ _ _)

/-- Successive physical boundary frames of the complete source compiler. -/
def canvasFrames (f : NumericFormula) : List (ℕ × List ℕ) :=
  frames f.1 (List.range f.1) (formulaStages f.1 f.2)

theorem canvasFrames_length (f : NumericFormula) : (canvasFrames f).length=formulaColumns f.1 f.2+1 := by
  simp [canvasFrames]

end PlanarHom.PositiveBlockProgram
