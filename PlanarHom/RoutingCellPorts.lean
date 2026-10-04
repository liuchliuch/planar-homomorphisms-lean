import PlanarHom.RoutingDistinctPorts

/-! Literal ordered signal ports of every grid cell, shared by the exact-one
and direct coloring realizations. Coordinates are combinatorial grid indices;
the physical point is (64*column,-64*row). -/
namespace PlanarHom.PositiveBlockProgram

def CellShape.portCount : CellShape → ℕ
  | .wireTop | .wireBottom | .wireDown => 2
  | .cross => 4
  | .fan | .test => 3

abbrev PortData := ℕ × (ℕ × ℕ)

/-- Variable index, then column and downward row; local port order is the
proved drawing's order, not a guessed geometric permutation. -/
def Cell.portData (c : Cell) : Fin c.shape.portCount → PortData :=
  match c.shape with
  | .wireTop => ![(c.args.1,c.column,c.row),(c.base,c.column+1,c.row)]
  | .wireBottom => ![(c.args.1,c.column,c.row+1),(c.base,c.column+1,c.row+1)]
  | .wireDown => ![(c.args.1,c.column,c.row),(c.base,c.column+1,c.row+1)]
  | .cross => ![(c.args.1,c.column,c.row+1),(c.args.2.1,c.column,c.row),
      (c.base,c.column+1,c.row),(c.base+1,c.column+1,c.row+1)]
  | .fan => ![(c.args.1,c.column,c.row),(c.base,c.column+1,c.row+1),(c.base+1,c.column+1,c.row)]
  | .test => ![(c.args.1,c.column,c.row),(c.args.2.1,c.column,c.row+1),(c.args.2.2,c.column,c.row+2)]

def Cell.outputRefs (c : Cell) : List ℕ :=
  match c.shape with
  | .wireTop | .wireBottom | .wireDown => [c.base]
  | .cross => [c.base,c.base+1]
  | .fan => [c.base+1,c.base]
  | .test => []

/-- Every port lies on a vertical cell boundary, at an explicitly bounded row. -/
theorem Cell.port_bounds (c : Cell) (i : Fin c.shape.portCount) :
    ((c.portData i).2.1=c.column ∨ (c.portData i).2.1=c.column+1) ∧
    c.row≤(c.portData i).2.2 ∧ (c.portData i).2.2≤c.row+c.shape.height := by
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases i <;> simp [Cell.portData,CellShape.height] <;> omega

/-- A cell's ports are geometrically distinct before any global gluing. -/
theorem Cell.port_positions_injective (c : Cell) : Function.Injective (fun i => (c.portData i).2) := by
  intro i j h
  rcases c with ⟨col,row,shape,base,args⟩
  cases shape <;> fin_cases i <;> fin_cases j
  all_goals simp [Cell.portData] at h ⊢
  all_goals omega

/-- Three different positions of a nonduplicated rail list name distinct
variables even when the corresponding source Boolean values are equal. -/
theorem getRef_ne (rs : List ℕ) (h : rs.Nodup) (i j : ℕ) (hi : i<rs.length) (hj : j<rs.length)
    (hne : i≠j) : getRef rs i≠getRef rs j := by
  simp only [getRef,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some]
  exact fun he => hne (h.getElem_inj_iff.mp he)

/-- The physical clause terminator always gets three distinct variable ports. -/
theorem clause_termination_distinct (n m : ℕ) (rs : List ℕ) (c : ParsimoniousNorOneInThree.Clause ℕ)
    (hr : ∀x∈rs,x<m) (hlen : rs.length=n)
    (hc : c.1<n ∧ c.2.1<n ∧ c.2.2<n) (hnd : rs.Nodup) :
    let out := (gatherClause n m rs c).rails
    getRef out n≠getRef out (n+1) ∧ getRef out n≠getRef out (n+2) ∧
      getRef out (n+1)≠getRef out (n+2) := by
  let out := (gatherClause n m rs c).rails
  have hl : out.length=n+3 := gatherClause_length n m rs c hr hlen hc
  have hn : out.Nodup := gatherClause_nodup n m rs c hnd
  exact ⟨getRef_ne out hn n (n+1) (by omega) (by omega) (by omega),
    getRef_ne out hn n (n+2) (by omega) (by omega) (by omega),
    getRef_ne out hn (n+1) (n+2) (by omega) (by omega) (by omega)⟩

end PlanarHom.PositiveBlockProgram
