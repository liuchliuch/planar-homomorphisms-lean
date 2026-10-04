import PlanarHom.PositiveRoutingLayers

/-! Static validity and explicit size bounds for actual numeric routing layers. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousBlockTemplate

structure LayerResult.WellFormed (m : ℕ) (r : LayerResult) : Prop where
  valid : Valid m r.instructions
  width_eq : width m r.instructions=r.variableCount
  rails_valid : ∀ x∈r.rails,x<r.variableCount

def prependBlock (op : Instruction) (outputs : List ℕ) (r : LayerResult) : LayerResult :=
  ⟨r.variableCount,outputs++r.rails,op::r.instructions⟩

/-- Every head output is freshly inside the physical local block. -/
theorem prependBlock_wellFormed (m : ℕ) (op : Instruction) (outputs : List ℕ) (r : LayerResult)
    (hop : ∀i,refs op i<m) (hout : ∀x∈outputs,x<m+op.1.template.fresh)
    (hr : r.WellFormed (m+op.1.template.fresh)) :
    (prependBlock op outputs r).WellFormed m := by
  refine ⟨⟨hop,hr.valid⟩,hr.width_eq,?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (hout x hx).trans_le ((width_ge _ _).trans_eq hr.width_eq)
  · exact hr.rails_valid x hx

theorem passive_wellFormed (m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x<m) :
    (passive m rs).WellFormed m :=
  ⟨wireProgram_valid m rs hr,wire_width m rs,fun x hx => (wireRails_bounds m rs x hx).2⟩

private theorem wire_refs (m x : ℕ) (hx : x<m) : ∀i,refs (wire x) i<m := by
  intro i
  change Fin 1 at i
  fin_cases i
  exact hx

private theorem crossing_refs (m a b : ℕ) (ha : a<m) (hb : b<m) : ∀i,refs (crossing a b) i<m := by
  intro i
  change Fin 2 at i
  fin_cases i
  · exact hb
  · exact ha

private theorem fan_refs (m a : ℕ) (ha : a<m) : ∀i,refs (fan a) i<m := by
  intro i
  change Fin 1 at i
  fin_cases i
  exact ha

theorem swapLayer_wellFormed (i m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x<m) :
    (swapLayer m i rs).WellFormed m := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => exact passive_wellFormed m [] hr
    | cons a rs =>
      cases rs with
      | nil => exact passive_wellFormed m [a] hr
      | cons b rs =>
        exact prependBlock_wellFormed m (crossing a b) [m,m+1] (passive (m+15) rs)
          (crossing_refs m a b (hr a (by simp)) (hr b (by simp)))
          (by intro x hx; change x<m+15; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega)
          (passive_wellFormed (m+15) rs (fun x hx => (hr x (by simp [hx])).trans_le (by omega)))
  | succ i ih =>
    cases rs with
    | nil => exact passive_wellFormed m [] hr
    | cons a rs =>
      exact prependBlock_wellFormed m (wire a) [m] (swapLayer (m+6) i rs)
        (wire_refs m a (hr a (by simp))) (by intro x hx; simp only [List.mem_singleton] at hx; subst x; change m<m+6; omega)
        (ih (m+6) rs (fun x hx => (hr x (by simp [hx])).trans_le (by omega)))

theorem copyLayer_wellFormed (i m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x<m) :
    (copyLayer m i rs).WellFormed m := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => exact passive_wellFormed m [] hr
    | cons a rs =>
      exact prependBlock_wellFormed m (fan a) [m+1,m] (passive (m+12) rs)
        (fan_refs m a (hr a (by simp)))
        (by intro x hx; change x<m+12; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega)
        (passive_wellFormed (m+12) rs (fun x hx => (hr x (by simp [hx])).trans_le (by omega)))
  | succ i ih =>
    cases rs with
    | nil => exact passive_wellFormed m [] hr
    | cons a rs =>
      exact prependBlock_wellFormed m (wire a) [m] (copyLayer (m+6) i rs)
        (wire_refs m a (hr a (by simp))) (by intro x hx; simp only [List.mem_singleton] at hx; subst x; change m<m+6; omega)
        (ih (m+6) rs (fun x hx => (hr x (by simp [hx])).trans_le (by omega)))

@[simp] theorem swapLayer_accepts (i m : ℕ) (rs : List ℕ) (xs : List Bool) :
    Accepts (swapLayer m i rs).instructions xs := by
  induction i generalizing m rs xs with
  | zero =>
    cases rs with
    | nil => trivial
    | cons a rs =>
      cases rs with
      | nil => exact wireProgram_accepts [a] xs
      | cons b rs => exact ⟨trivial,wireProgram_accepts rs _⟩
  | succ i ih =>
    cases rs with
    | nil => trivial
    | cons a rs => exact ⟨trivial,ih _ _ _⟩

@[simp] theorem copyLayer_accepts (i m : ℕ) (rs : List ℕ) (xs : List Bool) :
    Accepts (copyLayer m i rs).instructions xs := by
  induction i generalizing m rs xs with
  | zero =>
    cases rs with
    | nil => trivial
    | cons a rs => exact ⟨trivial,wireProgram_accepts rs _⟩
  | succ i ih =>
    cases rs with
    | nil => trivial
    | cons a rs => exact ⟨trivial,ih _ _ _⟩

theorem width_bound (m : ℕ) (ops : List Instruction) : width m ops≤m+15*ops.length := by
  induction ops generalizing m with
  | nil => simp [width]
  | cons op ops ih =>
    have hf : op.1.template.fresh≤15 := by cases op.1 <;> decide
    have h := ih (m+op.1.template.fresh)
    simp only [width,List.length_cons]
    omega

theorem swapLayer_instructions_length (i m : ℕ) (rs : List ℕ) :
    (swapLayer m i rs).instructions.length≤rs.length := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => simp [swapLayer,passive,wireProgram]
    | cons a rs => cases rs <;> simp [swapLayer,passive,wireProgram]
  | succ i ih =>
    cases rs with
    | nil => simp [swapLayer,passive,wireProgram]
    | cons a rs => simpa [swapLayer] using Nat.add_le_add_right (ih (m+6) rs) 1

theorem copyLayer_instructions_length (i m : ℕ) (rs : List ℕ) :
    (copyLayer m i rs).instructions.length=rs.length := by
  induction i generalizing m rs with
  | zero => cases rs <;> simp [copyLayer,passive,wireProgram]
  | succ i ih => cases rs <;> simp [copyLayer,passive,wireProgram,ih]

end PlanarHom.PositiveBlockProgram
