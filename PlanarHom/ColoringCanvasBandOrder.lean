import PlanarHom.ColoringRailBands

/-! The existing literal source canvas satisfies the stronger endpoint-band
order required by the exposed color/palette triples. No new input promise is
introduced; the proof follows the concrete swap, copy, and check renderers. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree AdjacentRailRouting

structure LocalColorBands (col leftRow rightRow : ℕ) (cs : List Cell) : Prop where
  columns : ∀ c∈cs,c.column=col
  left : ∀ c∈cs,leftRow≤c.row+c.shape.leftLo
  right : ∀ c∈cs,rightRow≤c.row+c.shape.rightLo
  ordered : cs.Pairwise Cell.ColorBandBefore

theorem LocalColorBands.cons (c : Cell) (cs : List Cell) (col lo ro : ℕ)
    (hc : c.column=col) (hl : lo≤c.row+c.shape.leftLo) (hr : ro≤c.row+c.shape.rightLo)
    (hcs : LocalColorBands col (c.row+c.shape.leftHi+1) (c.row+c.shape.rightHi+1) cs) :
    LocalColorBands col lo ro (c::cs) := by
  refine ⟨?_,?_,?_,List.pairwise_cons.mpr ⟨?_,hcs.ordered⟩⟩
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs.columns d hd
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hl
    · have h := hcs.left d hd
      have hlo : c.shape.leftLo≤c.shape.leftHi := by cases c.shape <;> decide
      omega
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hr
    · have h := hcs.right d hd
      have hlo : c.shape.rightLo≤c.shape.rightHi := by cases c.shape <;> decide
      omega
  · intro d hd
    exact Or.inr ⟨hc.trans (hcs.columns d hd).symm,by have := hcs.left d hd; omega,
      by have := hcs.right d hd; omega⟩

theorem wireCells_colorBands (shape : CellShape) (hl : shape.leftHi=shape.leftLo)
    (hr : shape.rightHi=shape.rightLo) (col row m : ℕ) (rs : List ℕ) :
    LocalColorBands col (row+shape.leftLo) (row+shape.rightLo) (wireCells shape col row m rs) := by
  induction rs generalizing row m with
  | nil => exact ⟨by simp [wireCells],by simp [wireCells],by simp [wireCells],List.Pairwise.nil⟩
  | cons a rs ih =>
    change LocalColorBands col (row+shape.leftLo) (row+shape.rightLo) (⟨col,row,shape,m,(a,0,0)⟩::wireCells shape col (row+1) (m+6) rs)
    apply LocalColorBands.cons ⟨col,row,shape,m,(a,0,0)⟩ (wireCells shape col (row+1) (m+6) rs) col (row+shape.leftLo) (row+shape.rightLo) rfl (le_refl _) (le_refl _)
    simpa only [hl,hr,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (row+1) (m+6)

theorem swapCells_colorBands (col row m i : ℕ) (rs : List ℕ) :
    LocalColorBands col row row (swapCells col row m i rs) := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => exact ⟨by simp [swapCells,wireCells],by simp [swapCells,wireCells],by simp [swapCells,wireCells],List.Pairwise.nil⟩
    | cons a rs =>
      cases rs with
      | nil => exact wireCells_colorBands .wireTop rfl rfl col row m [a]
      | cons b rs =>
        apply LocalColorBands.cons _ _ col row row rfl (by simp [CellShape.leftLo]) (by simp [CellShape.rightLo])
        exact wireCells_colorBands .wireBottom rfl rfl col (row+1) (m+15) rs
  | succ i ih =>
    cases rs with
    | nil => exact ⟨by simp [swapCells,wireCells],by simp [swapCells,wireCells],by simp [swapCells,wireCells],List.Pairwise.nil⟩
    | cons a rs =>
      exact LocalColorBands.cons _ _ col row row rfl (le_refl _) (le_refl _) (ih (row+1) (m+6) rs)

theorem copyCells_colorBands (col row m i : ℕ) (rs : List ℕ) :
    LocalColorBands col row row (copyCells col row m i rs) := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => exact ⟨by simp [copyCells],by simp [copyCells],by simp [copyCells],List.Pairwise.nil⟩
    | cons a rs =>
      apply LocalColorBands.cons _ _ col row row rfl (le_refl _) (le_refl _)
      exact wireCells_colorBands .wireDown rfl rfl col (row+1) (m+12) rs
  | succ i ih =>
    cases rs with
    | nil => exact ⟨by simp [copyCells],by simp [copyCells],by simp [copyCells],List.Pairwise.nil⟩
    | cons a rs =>
      exact LocalColorBands.cons _ _ col row row rfl (le_refl _) (le_refl _) (ih (row+1) (m+6) rs)

theorem checkCells_colorBands (col n m : ℕ) (rs : List ℕ) :
    LocalColorBands col 0 0 (checkCells col n m rs) := by
  have hw := wireCells_colorBands .wireTop rfl rfl col 0 m (rs.take n)
  refine ⟨?_,?_,?_,?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hw.columns c hc
    · exact congrArg Cell.column (List.mem_singleton.mp hc)
  · intro c _; exact Nat.zero_le _
  · intro c _; exact Nat.zero_le _
  · apply List.pairwise_append.mpr
    refine ⟨hw.ordered,by simp,?_⟩
    intro c hc d hd
    have he := List.mem_singleton.mp hd
    subst d
    have h := wireCells_mem .wireTop col 0 m (rs.take n) c hc
    have hn : (rs.take n).length≤n := List.length_take_le _ _
    apply Or.inr
    refine ⟨h.1,?_,?_⟩
    all_goals rw [h.2.1]; simp only [CellShape.leftHi,CellShape.rightHi,CellShape.leftLo,CellShape.rightLo,Nat.add_zero]; omega

structure ColorBandStrip (lo hi : ℕ) (cs : List Cell) : Prop where
  endpoints : lo≤hi
  columns : ∀ c∈cs,lo≤c.column ∧ c.column<hi
  ordered : cs.Pairwise Cell.ColorBandBefore

theorem LocalColorBands.strip {col lo ro : ℕ} {cs : List Cell} (h : LocalColorBands col lo ro cs) :
    ColorBandStrip col (col+1) cs :=
  ⟨by omega,fun c hc => by rw [h.columns c hc]; omega,h.ordered⟩

theorem ColorBandStrip.nil (col : ℕ) : ColorBandStrip col col [] :=
  ⟨le_refl _,by simp,List.Pairwise.nil⟩

theorem ColorBandStrip.append {lo mid hi : ℕ} {cs ds : List Cell}
    (hc : ColorBandStrip lo mid cs) (hd : ColorBandStrip mid hi ds) : ColorBandStrip lo hi (cs++ds) := by
  refine ⟨hc.endpoints.trans hd.endpoints,?_,?_⟩
  · intro c h
    rcases List.mem_append.mp h with h | h
    · have hh := hc.columns c h; exact ⟨hh.1,hh.2.trans_le hd.endpoints⟩
    · have hh := hd.columns c h; exact ⟨hc.endpoints.trans hh.1,hh.2⟩
  · apply List.pairwise_append.mpr
    exact ⟨hc.ordered,hd.ordered,fun c h d h' => Or.inl ((hc.columns c h).2.trans_le (hd.columns d h').1)⟩

theorem sweepCells_colorStrip (is : List ℕ) (col m : ℕ) (rs : List ℕ) :
    ColorBandStrip col (col+is.length) (sweepCells col m rs is) := by
  induction is generalizing col m rs with
  | nil => exact ColorBandStrip.nil col
  | cons i is ih =>
    have h := (swapCells_colorBands col 0 m i rs).strip.append
      (ih (col+1) (swapLayer m i rs).variableCount (swapLayer m i rs).rails)
    simpa only [sweepCells,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem macroCells_colorStrip (col n i m : ℕ) (rs : List ℕ) :
    ColorBandStrip col (col+copyColumns n i) (macroCells col n i m rs) := by
  by_cases hi : i<n
  · let is := moveScript i (n-1-i)
    let first := sweep m rs is
    let second := copyLayer first.variableCount (n-1) first.rails
    have h1 := sweepCells_colorStrip is col m rs
    have h2 := (copyCells_colorBands (col+is.length) 0 first.variableCount (n-1) first.rails).strip
    have h3 := sweepCells_colorStrip is.reverse (col+is.length+1) second.variableCount second.rails
    have h := (h1.append h2).append h3
    have he : col+is.length+1+is.reverse.length=col+copyColumns n i := by
      simp [is,copyColumns,hi]
      omega
    rw [he] at h
    simpa only [macroCells,if_pos hi] using h
  · simpa [macroCells,copyColumns,hi] using ColorBandStrip.nil col

theorem gatherCells_colorStrip (is : List ℕ) (col n m : ℕ) (rs : List ℕ) :
    ColorBandStrip col (col+gatherColumns n is) (gatherCells col n m rs is) := by
  induction is generalizing col m rs with
  | nil => simpa [gatherCells,gatherColumns] using ColorBandStrip.nil col
  | cons i is ih =>
    have h := (macroCells_colorStrip col n i m rs).append
      (ih (col+copyColumns n i) (copyMacro n i m rs).variableCount (copyMacro n i m rs).rails)
    simpa only [gatherCells,gatherColumns,List.map_cons,List.sum_cons,Nat.add_assoc] using h

theorem clauseCells_colorStrip (col n m : ℕ) (rs : List ℕ) (c : Clause ℕ) :
    ColorBandStrip col (col+clauseColumns n c) (clauseCells col n m rs c) := by
  have h := (gatherCells_colorStrip [c.1,c.2.1,c.2.2] col n m rs).append
    (checkCells_colorBands (col+gatherColumns n [c.1,c.2.1,c.2.2]) n
      (gatherClause n m rs c).variableCount (gatherClause n m rs c).rails).strip
  simpa only [clauseCells,clauseColumns,Nat.add_assoc] using h

theorem formulaCells_colorStrip (f : Formula ℕ) (col n m : ℕ) (rs : List ℕ) :
    ColorBandStrip col (col+formulaColumns n f) (formulaCells col n m rs f) := by
  induction f generalizing col m rs with
  | nil => simpa [formulaCells,formulaColumns] using ColorBandStrip.nil col
  | cons c cs ih =>
    have h := (clauseCells_colorStrip col n m rs c).append
      (ih (col+clauseColumns n c) (clauseLayer n m rs c).variableCount (clauseLayer n m rs c).rails)
    simpa only [formulaCells,formulaColumns,List.map_cons,List.sum_cons,Nat.add_assoc] using h

/-- Every generated canvas has disjoint positive-width coloring bands. -/
theorem canvas_colorBand_ordered (f : NumericFormula) : (canvas f).Pairwise Cell.ColorBandBefore :=
  (formulaCells_colorStrip f.2 0 f.1 f.1 (List.range f.1)).ordered

theorem canvas_colorBands_disjoint (f : NumericFormula) :
    Pairwise (fun i j : Fin (canvas f).length => Disjoint ((canvas f).get i).colorBand ((canvas f).get j).colorBand) := by
  intro i j hne
  have ho := List.pairwise_iff_get.mp (canvas_colorBand_ordered f)
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (ho i j hij).disjoint
  · exact (ho j i hji).disjoint.symm

end PlanarHom.PositiveBlockProgram
