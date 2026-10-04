import PlanarHom.RoutingPortCoherence

/-! Reachability, freshness, and boundary-port invariants of the actual stage
program. These are proved for the generated source program, not extra promises. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree

def Stage.Admissible (s : Stage) (rs : List ℕ) : Prop :=
  match s with
  | .swap _ | .copy _ => True
  | .check n => rs.length=n+3

def admissible (m : ℕ) (rs : List ℕ) : List Stage → Prop
  | [] => True
  | s::ss => s.Admissible rs ∧ admissible (s.render m rs).variableCount (s.render m rs).rails ss

theorem Stage.render_wellFormed (s : Stage) (m : ℕ) (rs : List ℕ)
    (hr : ∀x∈rs,x<m) (hs : s.Admissible rs) : (s.render m rs).WellFormed m := by
  cases s with
  | swap i => exact swapLayer_wellFormed i m rs hr
  | copy i => exact copyLayer_wellFormed i m rs hr
  | check n => exact checkLayer_wellFormed n m rs hr hs

theorem Stage.render_lower (s : Stage) (m : ℕ) (rs : List ℕ) (x : ℕ) (hx : x∈(s.render m rs).rails) : m≤x := by
  cases s with
  | swap i => exact swapLayer_lower i m rs x hx
  | copy i => exact copyLayer_lower i m rs x hx
  | check n => exact (wireRails_bounds m (rs.take n) x hx).1

theorem Stage.render_nodup (s : Stage) (m : ℕ) (rs : List ℕ) : (s.render m rs).rails.Nodup := by
  cases s with
  | swap i => exact swapLayer_nodup i m rs
  | copy i => exact copyLayer_nodup i m rs
  | check n => exact wireRails_nodup m (rs.take n)

theorem Stage.cells_ports (s : Stage) (col m : ℕ) (rs : List ℕ) (hs : s.Admissible rs)
    (c : Cell) (hc : c∈s.cells col m rs) (k : Fin c.shape.portCount) :
    c.portData k∈boundaryEntries col 0 rs++boundaryEntries (col+1) 0 (s.render m rs).rails := by
  cases s with
  | swap i => exact swapCells_ports col 0 m i rs c hc k
  | copy i => exact copyCells_ports col 0 m i rs c hc k
  | check n => exact checkCells_ports col n m rs hs c hc k

theorem Stage.cells_outputs (s : Stage) (col m : ℕ) (rs : List ℕ) :
    (s.cells col m rs).flatMap Cell.outputRefs=(s.render m rs).rails := by
  cases s with
  | swap i => exact swapCells_outputs col 0 m i rs
  | copy i => exact copyCells_outputs col 0 m i rs
  | check n => exact checkCells_outputs col n m rs

theorem admissible_append (ss ts : List Stage) (m : ℕ) (rs : List ℕ) :
    admissible m rs (ss++ts) ↔ admissible m rs ss ∧
      admissible (stages m rs ss).variableCount (stages m rs ss).rails ts := by
  induction ss generalizing m rs with
  | nil => simp [admissible,stages,LayerResult.identity]
  | cons s ss ih => simp only [List.cons_append,admissible,ih,stages,LayerResult.then,and_assoc]

theorem pure_stages_admissible (ss : List Stage)
    (h : ∀s∈ss,∀rs,s.Admissible rs) (m : ℕ) (rs : List ℕ) : admissible m rs ss := by
  induction ss generalizing m rs with
  | nil => trivial
  | cons s ss ih => exact ⟨h s (by simp) rs,ih (fun t ht => h t (by simp [ht])) _ _⟩

@[simp] theorem copyStages_admissible (n i m : ℕ) (rs : List ℕ) : admissible m rs (copyStages n i) := by
  apply pure_stages_admissible
  intro s hs rs'
  by_cases hi : i<n
  · simp only [copyStages,if_pos hi,List.mem_append,List.mem_map,List.mem_singleton] at hs
    rcases hs with (⟨j,_,rfl⟩ | rfl) | ⟨j,_,rfl⟩ <;> trivial
  · simp [copyStages,hi] at hs

@[simp] theorem gatherStages_admissible (is : List ℕ) (n m : ℕ) (rs : List ℕ) :
    admissible m rs (gatherStages n is) := by
  induction is generalizing m rs with
  | nil => trivial
  | cons i is ih =>
    apply (admissible_append _ _ _ _).mpr
    exact ⟨copyStages_admissible n i m rs,ih _ _⟩

theorem clauseStages_admissible (n m : ℕ) (rs : List ℕ) (c : Clause ℕ)
    (hr : ∀x∈rs,x<m) (hlen : rs.length=n) (hc : c.1<n ∧ c.2.1<n ∧ c.2.2<n) :
    admissible m rs (clauseStages n c) := by
  apply (admissible_append _ _ _ _).mpr
  refine ⟨gatherStages_admissible _ _ _ _,?_⟩
  rw [stages_gatherStages]
  exact ⟨gatherClause_length n m rs c hr hlen hc,trivial⟩

theorem formulaStages_admissible (f : Formula ℕ) (n m : ℕ) (rs : List ℕ)
    (hr : ∀x∈rs,x<m) (hlen : rs.length=n) (hf : NumericValid (n,f)) :
    admissible m rs (formulaStages n f) := by
  induction f generalizing m rs with
  | nil => trivial
  | cons c cs ih =>
    have hc := hf c (by simp)
    have hcs : NumericValid (n,cs) := fun d hd => hf d (by simp [hd])
    apply (admissible_append _ _ _ _).mpr
    refine ⟨clauseStages_admissible n m rs c hr hlen hc,?_⟩
    rw [stages_clauseStages]
    exact ih _ _ (clauseLayer_wellFormed n m rs c hr hlen hc).rails_valid
      (clauseLayer_length n m rs c hr hlen hc) hcs

theorem stages_wellFormed (ss : List Stage) (m : ℕ) (rs : List ℕ)
    (hr : ∀x∈rs,x<m) (hs : admissible m rs ss) : (stages m rs ss).WellFormed m := by
  induction ss generalizing m rs with
  | nil => exact ⟨trivial,rfl,hr⟩
  | cons s ss ih =>
    have hfirst := s.render_wellFormed m rs hr hs.1
    exact hfirst.then (ih _ _ hfirst.rails_valid hs.2)

end PlanarHom.PositiveBlockProgram
