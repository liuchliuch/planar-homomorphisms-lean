import PlanarHom.ColoringCanvasFrontierRun

/-! The actual complete source canvas executes by ordered boundary-block
substitution from its initial rails to its final rails. No planar-canvas
promise or guessed order is supplied as an input. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree AdjacentRailRouting

 theorem railFrontier_append (col row : ℕ) (xs ys : List ℕ) :
    railFrontier col row (xs++ys)=railFrontier col row xs++railFrontier col (row+xs.length) ys := by
  induction xs generalizing row with
  | nil => simp [railFrontier]
  | cons x xs ih => simp [railFrontier,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

 theorem list_eq_take_three (n : ℕ) (rs : List ℕ) (hlen : rs.length=n+3) :
    rs=rs.take n++[getRef rs n,getRef rs (n+1),getRef rs (n+2)] := by
  induction n generalizing rs with
  | zero =>
      obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hlen
      simp [getRef]
  | succ n ih =>
      cases rs with
      | nil => simp at hlen
      | cons a rs =>
          have ht : rs.length=n+3 := by simp only [List.length_cons] at hlen; omega
          have h := congrArg (List.cons a) (ih rs ht)
          simpa [getRef,Nat.add_assoc] using h

 theorem checkCells_leftFrontier (col n m : ℕ) (rs : List ℕ) (hlen : rs.length=n+3) :
    leftFrontier (checkCells col n m rs)=railFrontier col 0 rs := by
  have hn : (rs.take n).length=n := List.length_take_of_le (by omega)
  have ht := list_eq_take_three n rs hlen
  conv_rhs => rw [ht]
  rw [railFrontier_append,hn]
  simp only [checkCells,leftFrontier,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil]
  change leftFrontier (wireCells .wireTop col 0 m (rs.take n))++_= _
  rw [wireCells_leftFrontier .wireTop rfl]
  simp [Cell.leftFrontier,CellShape.leftPorts,Cell.portData,railFrontier]

 theorem checkCells_rightFrontier (col n m : ℕ) (rs : List ℕ) :
    rightFrontier (checkCells col n m rs)=railFrontier (col+1) 0 (checkLayer n m rs).rails := by
  simp only [checkCells,rightFrontier,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil]
  change rightFrontier (wireCells .wireTop col 0 m (rs.take n))++_=_
  rw [wireCells_rightFrontier .wireTop rfl]
  simp [Cell.rightFrontier,CellShape.rightPorts,checkLayer]

 theorem checkCells_frontierRun (col n m : ℕ) (rs : List ℕ) (hlen : rs.length=n+3) :
    FrontierRun (railFrontier col 0 rs) (checkCells col n m rs)
      (railFrontier (col+1) 0 (checkLayer n m rs).rails) := by
  simpa only [checkCells_leftFrontier col n m rs hlen,checkCells_rightFrontier] using
    frontierRun_column (checkCells col n m rs)

 theorem clauseCells_frontierRun (col n m : ℕ) (rs : List ℕ) (c : Clause ℕ)
    (hr : ∀x∈rs,x<m) (hlen : rs.length=n) (hc : c.1<n ∧ c.2.1<n ∧ c.2.2<n) :
    FrontierRun (railFrontier col 0 rs) (clauseCells col n m rs c)
      (railFrontier (col+clauseColumns n c) 0 (clauseLayer n m rs c).rails) := by
  have h := (gatherCells_frontierRun [c.1,c.2.1,c.2.2] col n m rs).append
    (checkCells_frontierRun (col+gatherColumns n [c.1,c.2.1,c.2.2]) n
      (gatherClause n m rs c).variableCount (gatherClause n m rs c).rails
      (gatherClause_length n m rs c hr hlen hc))
  simpa only [clauseCells,clauseLayer,gatherClause,LayerResult.then,clauseColumns,Nat.add_assoc] using h

 theorem formulaCells_frontierRun (f : Formula ℕ) (col n m : ℕ) (rs : List ℕ)
    (hr : ∀x∈rs,x<m) (hlen : rs.length=n) (hf : NumericValid (n,f)) :
    FrontierRun (railFrontier col 0 rs) (formulaCells col n m rs f)
      (railFrontier (col+formulaColumns n f) 0 (formulaLayers n m rs f).rails) := by
  induction f generalizing col m rs with
  | nil => exact .nil _
  | cons c cs ih =>
      have hc := hf c (by simp)
      have hw := clauseLayer_wellFormed n m rs c hr hlen hc
      have hl := clauseLayer_length n m rs c hr hlen hc
      have h := (clauseCells_frontierRun col n m rs c hr hlen hc).append
        (ih (col+clauseColumns n c) (clauseLayer n m rs c).variableCount
          (clauseLayer n m rs c).rails hw.rails_valid hl (fun d hd => hf d (by simp [hd])))
      simpa only [formulaCells,formulaLayers,formulaColumns,List.map_cons,List.sum_cons,
        LayerResult.then,Nat.add_assoc] using h

/-- The fully emitted numeric source has the exact boundary order required by
successive exterior-face attachments, including all fanout and termination steps. -/
 theorem canvas_frontierRun (f : NumericFormula) (hf : NumericValid f) :
    FrontierRun (railFrontier 0 0 (List.range f.1)) (canvas f)
      (railFrontier (formulaColumns f.1 f.2) 0
        (formulaLayers f.1 f.1 (List.range f.1) f.2).rails) := by
  simpa only [Nat.zero_add] using formulaCells_frontierRun f.2 0 f.1 f.1 (List.range f.1)
    (fun _ h => List.mem_range.mp h) (by simp) hf
end PlanarHom.PositiveBlockProgram
