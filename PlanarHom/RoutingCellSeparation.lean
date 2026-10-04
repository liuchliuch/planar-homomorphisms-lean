import PlanarHom.PlacedRoutingCells

/-! Explicit geometric nonoverlap of every rectangle in the generated routing
canvas. The proof follows actual column counts and emitted row order. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree AdjacentRailRouting MultiGraph

def Cell.Before (a b : Cell) : Prop :=
  a.column<b.column ∨ a.column=b.column ∧ a.row+a.shape.height≤b.row

structure LocalCells (col row : ℕ) (cs : List Cell) : Prop where
  columns : ∀ c∈cs,c.column=col
  rows : ∀ c∈cs,row≤c.row
  ordered : cs.Pairwise Cell.Before

theorem LocalCells.cons (c : Cell) (cs : List Cell) (col row : ℕ)
    (hc : c.column=col) (hr : row≤c.row) (hcs : LocalCells col (c.row+c.shape.height) cs) :
    LocalCells col row (c::cs) := by
  refine ⟨?_,?_,List.pairwise_cons.mpr ⟨?_,hcs.ordered⟩⟩
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs.columns d hd
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hr
    · have h := hcs.rows d hd; omega
  · intro d hd
    exact Or.inr ⟨hc.trans (hcs.columns d hd).symm,hcs.rows d hd⟩

theorem wireCells_mem (shape : CellShape) (col row m : ℕ) (rs : List ℕ) (c : Cell)
    (hc : c∈wireCells shape col row m rs) :
    c.column=col ∧ c.shape=shape ∧ row≤c.row ∧ c.row<row+rs.length := by
  induction rs generalizing row m with
  | nil => simp [wireCells] at hc
  | cons a rs ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · simp [List.length_cons]
    · have h := ih (row+1) (m+6) hc
      simp only [List.length_cons]
      exact ⟨h.1,h.2.1,by omega,by omega⟩

theorem wireCells_local (shape : CellShape) (hshape : shape.height=1) (col row m : ℕ) (rs : List ℕ) :
    LocalCells col row (wireCells shape col row m rs) := by
  induction rs generalizing row m with
  | nil => exact ⟨by simp [wireCells],by simp [wireCells],List.Pairwise.nil⟩
  | cons a rs ih =>
    apply LocalCells.cons _ _ col row rfl (le_refl row)
    simpa only [hshape] using ih (row+1) (m+6)

theorem swapCells_local (col row m i : ℕ) (rs : List ℕ) : LocalCells col row (swapCells col row m i rs) := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => exact wireCells_local .wireTop rfl col row m []
    | cons a rs =>
      cases rs with
      | nil => exact wireCells_local .wireTop rfl col row m [a]
      | cons b rs =>
        exact LocalCells.cons _ _ col row rfl (le_refl row)
          (wireCells_local .wireBottom rfl col (row+1) (m+15) rs)
  | succ i ih =>
    cases rs with
    | nil => exact wireCells_local .wireTop rfl col row m []
    | cons a rs => exact LocalCells.cons _ _ col row rfl (le_refl row) (ih (row+1) (m+6) rs)

theorem copyCells_local (col row m i : ℕ) (rs : List ℕ) : LocalCells col row (copyCells col row m i rs) := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => exact ⟨by simp [copyCells],by simp [copyCells],List.Pairwise.nil⟩
    | cons a rs =>
      exact LocalCells.cons _ _ col row rfl (le_refl row)
        (wireCells_local .wireDown rfl col (row+1) (m+12) rs)
  | succ i ih =>
    cases rs with
    | nil => exact ⟨by simp [copyCells],by simp [copyCells],List.Pairwise.nil⟩
    | cons a rs => exact LocalCells.cons _ _ col row rfl (le_refl row) (ih (row+1) (m+6) rs)

theorem checkCells_local (col n m : ℕ) (rs : List ℕ) : LocalCells col 0 (checkCells col n m rs) := by
  have hw := wireCells_local .wireTop rfl col 0 m (rs.take n)
  refine ⟨?_,?_,?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hw.columns c hc
    · exact congrArg Cell.column (List.mem_singleton.mp hc)
  · intro c _
    exact Nat.zero_le c.row
  · apply List.pairwise_append.mpr
    refine ⟨hw.ordered,by simp,?_⟩
    intro c hc d hd
    have he := List.mem_singleton.mp hd
    subst d
    have h := wireCells_mem .wireTop col 0 m (rs.take n) c hc
    have hn : (rs.take n).length≤n := List.length_take_le _ _
    exact Or.inr ⟨h.1,by rw [h.2.1]; change c.row+1≤n; omega⟩

structure CellStrip (lo hi : ℕ) (cs : List Cell) : Prop where
  endpoints : lo≤hi
  columns : ∀ c∈cs,lo≤c.column ∧ c.column<hi
  ordered : cs.Pairwise Cell.Before

theorem LocalCells.strip {col row : ℕ} {cs : List Cell} (h : LocalCells col row cs) :
    CellStrip col (col+1) cs :=
  ⟨by omega,fun c hc => by rw [h.columns c hc]; omega,h.ordered⟩

theorem CellStrip.nil (col : ℕ) : CellStrip col col [] :=
  ⟨le_refl _,by simp,List.Pairwise.nil⟩

theorem CellStrip.append {lo mid hi : ℕ} {cs ds : List Cell}
    (hc : CellStrip lo mid cs) (hd : CellStrip mid hi ds) : CellStrip lo hi (cs++ds) := by
  refine ⟨hc.endpoints.trans hd.endpoints,?_,?_⟩
  · intro c h
    rcases List.mem_append.mp h with h | h
    · have hh := hc.columns c h; exact ⟨hh.1,hh.2.trans_le hd.endpoints⟩
    · have hh := hd.columns c h; exact ⟨hc.endpoints.trans hh.1,hh.2⟩
  · apply List.pairwise_append.mpr
    exact ⟨hc.ordered,hd.ordered,fun c h d h' => Or.inl ((hc.columns c h).2.trans_le (hd.columns d h').1)⟩

theorem sweepCells_strip (is : List ℕ) (col m : ℕ) (rs : List ℕ) :
    CellStrip col (col+is.length) (sweepCells col m rs is) := by
  induction is generalizing col m rs with
  | nil => exact CellStrip.nil col
  | cons i is ih =>
    have h := (swapCells_local col 0 m i rs).strip.append
      (ih (col+1) (swapLayer m i rs).variableCount (swapLayer m i rs).rails)
    simpa only [sweepCells,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem macroCells_strip (col n i m : ℕ) (rs : List ℕ) :
    CellStrip col (col+copyColumns n i) (macroCells col n i m rs) := by
  by_cases hi : i<n
  · let is := moveScript i (n-1-i)
    let first := sweep m rs is
    let second := copyLayer first.variableCount (n-1) first.rails
    have h1 := sweepCells_strip is col m rs
    have h2 := (copyCells_local (col+is.length) 0 first.variableCount (n-1) first.rails).strip
    have h3 := sweepCells_strip is.reverse (col+is.length+1) second.variableCount second.rails
    have h := (h1.append h2).append h3
    have he : col+is.length+1+is.reverse.length=col+copyColumns n i := by
      simp [is,copyColumns,hi]
      omega
    rw [he] at h
    simpa only [macroCells,if_pos hi] using h
  · simpa [macroCells,copyColumns,hi] using CellStrip.nil col

theorem gatherCells_strip (is : List ℕ) (col n m : ℕ) (rs : List ℕ) :
    CellStrip col (col+gatherColumns n is) (gatherCells col n m rs is) := by
  induction is generalizing col m rs with
  | nil => simpa [gatherCells,gatherColumns] using CellStrip.nil col
  | cons i is ih =>
    have h := (macroCells_strip col n i m rs).append
      (ih (col+copyColumns n i) (copyMacro n i m rs).variableCount (copyMacro n i m rs).rails)
    simpa only [gatherCells,gatherColumns,List.map_cons,List.sum_cons,Nat.add_assoc] using h

theorem clauseCells_strip (col n m : ℕ) (rs : List ℕ) (c : Clause ℕ) :
    CellStrip col (col+clauseColumns n c) (clauseCells col n m rs c) := by
  have h := (gatherCells_strip [c.1,c.2.1,c.2.2] col n m rs).append
    (checkCells_local (col+gatherColumns n [c.1,c.2.1,c.2.2]) n
      (gatherClause n m rs c).variableCount (gatherClause n m rs c).rails).strip
  simpa only [clauseCells,clauseColumns,Nat.add_assoc] using h

theorem formulaCells_strip (f : Formula ℕ) (col n m : ℕ) (rs : List ℕ) :
    CellStrip col (col+formulaColumns n f) (formulaCells col n m rs f) := by
  induction f generalizing col m rs with
  | nil => simpa [formulaCells,formulaColumns] using CellStrip.nil col
  | cons c cs ih =>
    have h := (clauseCells_strip col n m rs c).append
      (ih (col+clauseColumns n c) (clauseLayer n m rs c).variableCount (clauseLayer n m rs c).rails)
    simpa only [formulaCells,formulaColumns,List.map_cons,List.sum_cons,Nat.add_assoc] using h

/-- Actual emitted cells are strictly ordered by nonoverlapping rectangle bands. -/
theorem canvas_ordered (f : NumericFormula) : (canvas f).Pairwise Cell.Before :=
  (formulaCells_strip f.2 0 f.1 f.1 (List.range f.1)).ordered

/-- Ordered cell bands have actually disjoint open geometric regions. -/
theorem Cell.Before.region_disjoint {a b : Cell} (h : a.Before b) : Disjoint a.region b.region := by
  apply Set.disjoint_left.mpr
  intro p ha hb
  rcases ha with ⟨hax0,hax1,hay0,hay1⟩
  rcases hb with ⟨hbx0,hbx1,hby0,hby1⟩
  rcases h with h | ⟨_,h⟩
  · have hi : a.column+1≤b.column := by omega
    have hr : (a.column:ℝ)+1≤b.column := by exact_mod_cast hi
    linarith
  · have hr : ((a.row+a.shape.height:ℕ):ℝ)≤b.row := by exact_mod_cast h
    linarith

/-- Pairwise disjoint actual placement regions for the entire emitted canvas. -/
theorem canvas_regions_disjoint (f : NumericFormula) :
    Pairwise (fun i j : Fin (canvas f).length => Disjoint ((canvas f).get i).region ((canvas f).get j).region) := by
  intro i j hne
  have ho := List.pairwise_iff_get.mp (canvas_ordered f)
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (ho i j hij).region_disjoint
  · exact (ho j i hji).region_disjoint.symm

end PlanarHom.PositiveBlockProgram
