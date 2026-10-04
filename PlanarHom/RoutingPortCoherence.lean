import PlanarHom.RoutingStageProgram
import PlanarHom.RoutingCellPorts

/-! Exact named signal ports on the two boundary frames of every physical
routing layer. This is the combinatorial name/location gluing invariant. -/
namespace PlanarHom.PositiveBlockProgram

def boundaryEntries (col row : ℕ) : List ℕ → List PortData
  | [] => []
  | r::rs => (r,col,row)::boundaryEntries col (row+1) rs

@[simp] theorem boundaryEntries_append (col row : ℕ) (rs ts : List ℕ) :
    boundaryEntries col row (rs++ts)=boundaryEntries col row rs++boundaryEntries col (row+rs.length) ts := by
  induction rs generalizing row with
  | nil => simp [boundaryEntries]
  | cons r rs ih => simp [boundaryEntries,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem extend_entries (p : PortData) (col oldRow newRow : ℕ)
    (oldPre newPre oldTail newTail : List ℕ)
    (hp : p∈boundaryEntries col (oldRow+oldPre.length) oldTail++
      boundaryEntries (col+1) (newRow+newPre.length) newTail) :
    p∈boundaryEntries col oldRow (oldPre++oldTail)++boundaryEntries (col+1) newRow (newPre++newTail) := by
  rw [boundaryEntries_append,boundaryEntries_append]
  rcases List.mem_append.mp hp with hp | hp
  · exact List.mem_append_left _ (List.mem_append_right _ hp)
  · exact List.mem_append_right _ (List.mem_append_right _ hp)

def CellShape.inputOffset : CellShape → ℕ
  | .wireBottom => 1
  | _ => 0

def CellShape.outputOffset : CellShape → ℕ
  | .wireBottom | .wireDown => 1
  | _ => 0

theorem wireCells_ports (shape : CellShape) (hshape : shape.kind=.wire) (col row m : ℕ)
    (rs : List ℕ) (c : Cell) (hc : c∈wireCells shape col row m rs) (k : Fin c.shape.portCount) :
    c.portData k∈boundaryEntries col (row+shape.inputOffset) rs++
      boundaryEntries (col+1) (row+shape.outputOffset) (wireRails m rs) := by
  have hcases : shape=.wireTop ∨ shape=.wireBottom ∨ shape=.wireDown := by
    cases shape <;> simp_all [CellShape.kind]
  rcases hcases with rfl | rfl | rfl
  all_goals induction rs generalizing row m with
  | nil => simp [wireCells] at hc
  | cons a rs ih =>
    rcases List.mem_cons.mp hc with he | hc
    · subst c
      change Fin 2 at k
      fin_cases k <;> simp [Cell.portData,boundaryEntries,wireRails,CellShape.inputOffset,CellShape.outputOffset]
    · have h := ih (row+1) (m+6) hc
      apply extend_entries (c.portData k) col _ _ [a] [m] rs (wireRails (m+6) rs)
      simpa only [List.length_singleton,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Every port of an adjacent-crossing layer belongs to exactly the announced
input or fresh output boundary frame. -/
theorem swapCells_ports (col row m i : ℕ) (rs : List ℕ) (c : Cell)
    (hc : c∈swapCells col row m i rs) (k : Fin c.shape.portCount) :
    c.portData k∈boundaryEntries col row rs++boundaryEntries (col+1) row (swapLayer m i rs).rails := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => simp [swapCells,wireCells] at hc
    | cons a rs =>
      cases rs with
      | nil => exact wireCells_ports .wireTop rfl col row m [a] c hc k
      | cons b rs =>
        rcases List.mem_cons.mp hc with he | hc
        · subst c
          change Fin 4 at k
          fin_cases k <;> simp [Cell.portData,boundaryEntries,swapLayer,passive,wireRails,
            Matrix.cons_val_two,Matrix.cons_val_three]
        · have h := wireCells_ports .wireBottom rfl col (row+1) (m+15) rs c hc k
          apply extend_entries (c.portData k) col row row [a,b] [m,m+1] rs (wireRails (m+15) rs)
          simpa [CellShape.inputOffset,CellShape.outputOffset,Nat.add_assoc] using h
  | succ i ih =>
    cases rs with
    | nil => simp [swapCells,wireCells] at hc
    | cons a rs =>
      rcases List.mem_cons.mp hc with he | hc
      · subst c
        change Fin 2 at k
        fin_cases k <;> simp [Cell.portData,boundaryEntries,swapLayer]
      · have h := ih (row+1) (m+6) rs hc
        apply extend_entries (c.portData k) col row row [a] [m] rs (swapLayer (m+6) i rs).rails
        simpa only [List.length_singleton] using h

/-- Lower passive rails shift down exactly once during fanout. -/
theorem copyCells_ports (col row m i : ℕ) (rs : List ℕ) (c : Cell)
    (hc : c∈copyCells col row m i rs) (k : Fin c.shape.portCount) :
    c.portData k∈boundaryEntries col row rs++boundaryEntries (col+1) row (copyLayer m i rs).rails := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => simp [copyCells] at hc
    | cons a rs =>
      rcases List.mem_cons.mp hc with he | hc
      · subst c
        change Fin 3 at k
        fin_cases k <;> simp [Cell.portData,boundaryEntries,copyLayer,passive,wireRails,Matrix.cons_val_two]
      · have h := wireCells_ports .wireDown rfl col (row+1) (m+12) rs c hc k
        apply extend_entries (c.portData k) col row row [a] [m+1,m] rs (wireRails (m+12) rs)
        simpa [CellShape.inputOffset,CellShape.outputOffset,Nat.add_assoc] using h
  | succ i ih =>
    cases rs with
    | nil => simp [copyCells] at hc
    | cons a rs =>
      rcases List.mem_cons.mp hc with he | hc
      · subst c
        change Fin 2 at k
        fin_cases k <;> simp [Cell.portData,boundaryEntries,copyLayer]
      · have h := ih (row+1) (m+6) rs hc
        apply extend_entries (c.portData k) col row row [a] [m] rs (copyLayer (m+6) i rs).rails
        simpa only [List.length_singleton] using h

theorem boundaryEntries_get (col row : ℕ) (rs : List ℕ) (i : ℕ) (hi : i<rs.length) :
    (getRef rs i,col,row+i)∈boundaryEntries col row rs := by
  induction rs generalizing row i with
  | nil => simp at hi
  | cons a rs ih =>
    cases i with
    | zero => simp [getRef,boundaryEntries]
    | succ i =>
      have h := ih (row+1) i (by simpa using hi)
      apply List.mem_cons_of_mem
      simpa [getRef,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem boundaryEntries_take_subset (col row n : ℕ) (rs : List ℕ) (p : PortData)
    (hp : p∈boundaryEntries col row (rs.take n)) : p∈boundaryEntries col row rs := by
  have h := List.mem_append_left (boundaryEntries col (row+(rs.take n).length) (rs.drop n)) hp
  rw [←boundaryEntries_append,List.take_append_drop] at h
  exact h

theorem checkCells_ports (col n m : ℕ) (rs : List ℕ) (hlen : rs.length=n+3)
    (c : Cell) (hc : c∈checkCells col n m rs) (k : Fin c.shape.portCount) :
    c.portData k∈boundaryEntries col 0 rs++boundaryEntries (col+1) 0 (checkLayer n m rs).rails := by
  rcases List.mem_append.mp hc with hc | hc
  · have h := wireCells_ports .wireTop rfl col 0 m (rs.take n) c hc k
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (boundaryEntries_take_subset col 0 n rs _ h)
    · exact List.mem_append_right _ h
  · have he := List.mem_singleton.mp hc
    subst c
    change Fin 3 at k
    fin_cases k
    · exact List.mem_append_left _ (by simpa [Cell.portData] using boundaryEntries_get col 0 rs n (by omega))
    · exact List.mem_append_left _ (by simpa [Cell.portData] using boundaryEntries_get col 0 rs (n+1) (by omega))
    · exact List.mem_append_left _ (by simpa [Cell.portData,Matrix.cons_val_two] using boundaryEntries_get col 0 rs (n+2) (by omega))

theorem wireCells_outputs (shape : CellShape) (hs : shape.kind=.wire) (col row m : ℕ) (rs : List ℕ) :
    (wireCells shape col row m rs).flatMap Cell.outputRefs=wireRails m rs := by
  have hcases : shape=.wireTop ∨ shape=.wireBottom ∨ shape=.wireDown := by
    cases shape <;> simp_all [CellShape.kind]
  rcases hcases with rfl | rfl | rfl
  all_goals induction rs generalizing row m with
  | nil => rfl
  | cons a rs ih => simp [wireCells,Cell.outputRefs,wireRails,ih]

theorem swapCells_outputs (col row m i : ℕ) (rs : List ℕ) :
    (swapCells col row m i rs).flatMap Cell.outputRefs=(swapLayer m i rs).rails := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      cases rs with
      | nil => exact wireCells_outputs .wireTop rfl col row m [a]
      | cons b rs => simp [swapCells,swapLayer,passive,Cell.outputRefs,wireCells_outputs,CellShape.kind]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs => simp [swapCells,swapLayer,Cell.outputRefs,ih]

theorem copyCells_outputs (col row m i : ℕ) (rs : List ℕ) :
    (copyCells col row m i rs).flatMap Cell.outputRefs=(copyLayer m i rs).rails := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs => simp [copyCells,copyLayer,passive,Cell.outputRefs,wireCells_outputs,CellShape.kind]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs => simp [copyCells,copyLayer,Cell.outputRefs,ih]

theorem checkCells_outputs (col n m : ℕ) (rs : List ℕ) :
    (checkCells col n m rs).flatMap Cell.outputRefs=(checkLayer n m rs).rails := by
  simp [checkCells,checkLayer,Cell.outputRefs,wireCells_outputs,CellShape.kind]

end PlanarHom.PositiveBlockProgram
