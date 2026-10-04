import PlanarHom.RoutingBoundaryRegistry

/-! Exact contiguous fresh-variable allocation along the geometric cell trace.
This links cell-local indices literally to the materialized numeric formula. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree

def Cell.fresh (c : Cell) : ℕ := c.instruction.1.template.fresh

def BaseSequence (m : ℕ) : List Cell → Prop
  | [] => True
  | c::cs => c.base=m ∧ BaseSequence (m+c.fresh) cs

theorem baseSequence_append (cs ds : List Cell) (m : ℕ) :
    BaseSequence m (cs++ds) ↔ BaseSequence m cs ∧ BaseSequence (width m (cs.map Cell.instruction)) ds := by
  induction cs generalizing m with
  | nil => simp [BaseSequence,width]
  | cons c cs ih => simp only [List.cons_append,BaseSequence,ih,List.map_cons,width,Cell.fresh,and_assoc]

theorem wireCells_bases (shape : CellShape) (hshape : shape.kind=.wire) (col row m : ℕ) (rs : List ℕ) :
    BaseSequence m (wireCells shape col row m rs) := by
  induction rs generalizing row m with
  | nil => trivial
  | cons a rs ih =>
    refine ⟨rfl,?_⟩
    simpa only [Cell.fresh,Cell.instruction,hshape,Kind.template,ParsimoniousBlockTemplate.equality] using ih (row+1) (m+6)

theorem swapCells_bases (col row m i : ℕ) (rs : List ℕ) : BaseSequence m (swapCells col row m i rs) := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => trivial
    | cons a rs =>
      cases rs with
      | nil => exact wireCells_bases .wireTop rfl col row m [a]
      | cons b rs => exact ⟨rfl,wireCells_bases .wireBottom rfl col (row+1) (m+15) rs⟩
  | succ i ih =>
    cases rs with
    | nil => trivial
    | cons a rs => exact ⟨rfl,ih (row+1) (m+6) rs⟩

theorem copyCells_bases (col row m i : ℕ) (rs : List ℕ) : BaseSequence m (copyCells col row m i rs) := by
  induction i generalizing row m rs with
  | zero =>
    cases rs with
    | nil => trivial
    | cons a rs => exact ⟨rfl,wireCells_bases .wireDown rfl col (row+1) (m+12) rs⟩
  | succ i ih =>
    cases rs with
    | nil => trivial
    | cons a rs => exact ⟨rfl,ih (row+1) (m+6) rs⟩

theorem checkCells_bases (col n m : ℕ) (rs : List ℕ) : BaseSequence m (checkCells col n m rs) := by
  apply (baseSequence_append _ _ m).mpr
  refine ⟨wireCells_bases .wireTop rfl col 0 m (rs.take n),?_⟩
  rw [wireCells_erase .wireTop rfl,wire_width]
  exact ⟨rfl,trivial⟩

theorem Stage.cells_bases (s : Stage) (col m : ℕ) (rs : List ℕ) : BaseSequence m (s.cells col m rs) := by
  cases s with
  | swap i => exact swapCells_bases col 0 m i rs
  | copy i => exact copyCells_bases col 0 m i rs
  | check n => exact checkCells_bases col n m rs

theorem Stage.cells_erase (s : Stage) (col m : ℕ) (rs : List ℕ) :
    (s.cells col m rs).map Cell.instruction=(s.render m rs).instructions := by
  cases s with
  | swap i => exact swapCells_erase col 0 m i rs
  | copy i => exact copyCells_erase col 0 m i rs
  | check n => exact checkCells_erase col n m rs

theorem stagesCells_bases (ss : List Stage) (col m : ℕ) (rs : List ℕ)
    (hr : ∀x∈rs,x<m) (hs : admissible m rs ss) : BaseSequence m (stagesCells col m rs ss) := by
  induction ss generalizing col m rs with
  | nil => trivial
  | cons s ss ih =>
    have hf := s.render_wellFormed m rs hr hs.1
    apply (baseSequence_append _ _ m).mpr
    refine ⟨s.cells_bases col m rs,?_⟩
    rw [s.cells_erase col m rs,hf.width_eq]
    exact ih (col+1) _ _ hf.rails_valid hs.2

theorem canvas_bases (f : NumericFormula) (hf : NumericValid f) : BaseSequence f.1 (canvas f) := by
  have h := stagesCells_bases (formulaStages f.1 f.2) 0 f.1 (List.range f.1)
    (fun x hx => List.mem_range.mp hx)
    (formulaStages_admissible f.2 f.1 f.1 (List.range f.1) (fun x hx => List.mem_range.mp hx) (by simp) hf)
  simpa only [stagesCells_formulaStages] using h

theorem baseSequence_bounds (cs : List Cell) (m : ℕ) (h : BaseSequence m cs) (c : Cell) (hc : c∈cs) :
    m≤c.base ∧ c.base+c.fresh≤width m (cs.map Cell.instruction) := by
  induction cs generalizing m with
  | nil => simp at hc
  | cons d ds ih =>
    obtain ⟨hd,ht⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [hd]
      exact ⟨le_refl _,width_ge (m+c.fresh) (ds.map Cell.instruction)⟩
    · have hh := ih (m+d.fresh) ht hc
      exact ⟨by omega,hh.2⟩

theorem baseSequence_ordered (cs : List Cell) (m : ℕ) (h : BaseSequence m cs) :
    cs.Pairwise (fun c d => c.base+c.fresh≤d.base) := by
  induction cs generalizing m with
  | nil => exact List.Pairwise.nil
  | cons c cs ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih (m+c.fresh) h.2⟩
    intro d hd
    have hb := (baseSequence_bounds cs (m+c.fresh) h.2 d hd).1
    simpa [h.1] using hb

theorem network_cells (cs : List Cell) (m : ℕ) (h : BaseSequence m cs) :
    network m (cs.map Cell.instruction)=
      cs.flatMap (fun c => c.instruction.1.template.emit c.base (refs c.instruction)) := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨hc,ht⟩ := h
    simp only [List.map_cons,network,List.flatMap_cons]
    have hh := ih (m+c.fresh) ht
    change network (m+c.instruction.1.template.fresh) (cs.map Cell.instruction)=_ at hh
    rw [hh,hc]

/-- Literal formula-list correspondence: all emitted cell clauses and numeric
variable references agree, including repeated source clauses. -/
theorem compile_clauses_eq_cells (f : NumericFormula) (hf : NumericValid f) :
    (PositiveRoutingCompiler.compile f).2=
      (canvas f).flatMap (fun c => c.instruction.1.template.emit c.base (refs c.instruction)) := by
  change network f.1 (PositiveRoutingCompiler.program f)=_
  rw [←canvas_erase]
  exact network_cells (canvas f) f.1 (canvas_bases f hf)

end PlanarHom.PositiveBlockProgram
