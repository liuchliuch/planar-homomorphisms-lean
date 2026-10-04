import PlanarHom.ColoringCanvasFrontiers

/-! Literal sequential boundary substitution for the emitted source canvas.
Only an ordered active subsequence of the exterior boundary is tracked; old
vertices and frame markers may remain between future attachment ports. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree AdjacentRailRouting

 inductive FrontierRun : List PortData → List Cell → List PortData → Prop
  | nil (xs) : FrontierRun xs [] xs
  | cons (pre post : List PortData) (c : Cell) (cs : List Cell) (ys : List PortData)
      (tail : FrontierRun (pre++c.rightFrontier++post) cs ys) :
      FrontierRun (pre++c.leftFrontier++post) (c::cs) ys

 theorem FrontierRun.append {xs ys zs : List PortData} {cs ds : List Cell}
    (h : FrontierRun xs cs ys) (k : FrontierRun ys ds zs) : FrontierRun xs (cs++ds) zs := by
  induction h with
  | nil => exact k
  | cons pre post c cs ys h ih => exact FrontierRun.cons pre post c _ _ (ih k)

 theorem FrontierRun.context {xs ys : List PortData} {cs : List Cell}
    (h : FrontierRun xs cs ys) (pre post : List PortData) :
    FrontierRun (pre++xs++post) cs (pre++ys++post) := by
  induction h with
  | nil => exact .nil _
  | cons p q c cs ys h ih =>
      simpa only [List.append_assoc] using
        FrontierRun.cons (pre++p) (q++post) c cs (pre++ys++post)
          (by simpa only [List.append_assoc] using ih)

 theorem frontierRun_column (cs : List Cell) : FrontierRun (leftFrontier cs) cs (rightFrontier cs) := by
  induction cs with
  | nil => exact .nil _
  | cons c cs ih =>
      simpa only [List.nil_append,leftFrontier_cons,rightFrontier_cons,List.append_nil] using
        FrontierRun.cons [] (leftFrontier cs) c cs (c.rightFrontier++rightFrontier cs)
          (by simpa using ih.context c.rightFrontier [])

 theorem swapCells_frontierRun (col row m i : ℕ) (rs : List ℕ) :
    FrontierRun (railFrontier col row rs) (swapCells col row m i rs)
      (railFrontier (col+1) row (swapLayer m i rs).rails) := by
  simpa only [swapCells_leftFrontier,swapCells_rightFrontier] using
    frontierRun_column (swapCells col row m i rs)

 theorem copyCells_frontierRun (col row m i : ℕ) (rs : List ℕ) :
    FrontierRun (railFrontier col row rs) (copyCells col row m i rs)
      (railFrontier (col+1) row (copyLayer m i rs).rails) := by
  simpa only [copyCells_leftFrontier,copyCells_rightFrontier] using
    frontierRun_column (copyCells col row m i rs)

 theorem sweepCells_frontierRun (is : List ℕ) (col m : ℕ) (rs : List ℕ) :
    FrontierRun (railFrontier col 0 rs) (sweepCells col m rs is)
      (railFrontier (col+is.length) 0 (sweep m rs is).rails) := by
  induction is generalizing col m rs with
  | nil => exact .nil _
  | cons i is ih =>
      have h := (swapCells_frontierRun col 0 m i rs).append
        (ih (col+1) (swapLayer m i rs).variableCount (swapLayer m i rs).rails)
      simpa only [sweepCells,sweep,LayerResult.then,List.length_cons,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using h

 theorem macroCells_frontierRun (col n i m : ℕ) (rs : List ℕ) :
    FrontierRun (railFrontier col 0 rs) (macroCells col n i m rs)
      (railFrontier (col+copyColumns n i) 0 (copyMacro n i m rs).rails) := by
  by_cases hi : i<n
  · let is := moveScript i (n-1-i)
    let first := sweep m rs is
    let second := copyLayer first.variableCount (n-1) first.rails
    have h1 := sweepCells_frontierRun is col m rs
    have h2 := copyCells_frontierRun (col+is.length) 0 first.variableCount (n-1) first.rails
    have h3 := sweepCells_frontierRun is.reverse (col+is.length+1) second.variableCount second.rails
    have h := (h1.append h2).append h3
    have he : col+is.length+1+is.reverse.length=col+copyColumns n i := by
      simp [is,copyColumns,hi]
      omega
    rw [he] at h
    simpa only [macroCells,copyMacro,if_pos hi,LayerResult.then,List.append_assoc] using h
  · simpa [macroCells,copyMacro,copyColumns,hi,LayerResult.identity] using
      FrontierRun.nil (railFrontier col 0 rs)

 theorem gatherCells_frontierRun (is : List ℕ) (col n m : ℕ) (rs : List ℕ) :
    FrontierRun (railFrontier col 0 rs) (gatherCells col n m rs is)
      (railFrontier (col+gatherColumns n is) 0 (gatherMacro n m rs is).rails) := by
  induction is generalizing col m rs with
  | nil => exact .nil _
  | cons i is ih =>
      have h := (macroCells_frontierRun col n i m rs).append
        (ih (col+copyColumns n i) (copyMacro n i m rs).variableCount (copyMacro n i m rs).rails)
      simpa only [gatherCells,gatherMacro,gatherColumns,List.map_cons,List.sum_cons,
        LayerResult.then,Nat.add_assoc] using h
end PlanarHom.PositiveBlockProgram
