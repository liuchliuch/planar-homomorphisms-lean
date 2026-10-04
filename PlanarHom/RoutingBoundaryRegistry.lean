import PlanarHom.RoutingStageInvariants

/-! A finite bijective registry between materialized boundary-variable names
and their grid coordinates. New layer outputs are fresh and the column strictly
increases, so both projections are injective. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree

@[simp] theorem boundaryEntries_refs (col row : ℕ) (rs : List ℕ) :
    (boundaryEntries col row rs).map Prod.fst=rs := by
  induction rs generalizing row with
  | nil => rfl
  | cons a rs ih => simp [boundaryEntries,ih]

theorem boundaryEntries_ref_mem (col row : ℕ) (rs : List ℕ) (p : PortData)
    (hp : p∈boundaryEntries col row rs) : p.1∈rs := by
  rw [←boundaryEntries_refs col row rs]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

theorem boundaryEntries_position (col row : ℕ) (rs : List ℕ) (p : PortData)
    (hp : p∈boundaryEntries col row rs) : p.2.1=col ∧ row≤p.2.2 := by
  induction rs generalizing row with
  | nil => simp [boundaryEntries] at hp
  | cons a rs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨rfl,le_refl _⟩
    · have h := ih (row+1) hp
      exact ⟨h.1,by omega⟩

theorem boundaryEntries_positions_nodup (col row : ℕ) (rs : List ℕ) :
    ((boundaryEntries col row rs).map Prod.snd).Nodup := by
  induction rs generalizing row with
  | nil => simp [boundaryEntries]
  | cons a rs ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih (row+1)⟩
    intro h
    obtain ⟨p,hp,he⟩ := List.mem_map.mp h
    have hr := (boundaryEntries_position col (row+1) rs p hp).2
    have hy := congrArg Prod.snd he
    dsimp only at hy
    omega

def registry (col m : ℕ) (rs : List ℕ) : List Stage → List PortData
  | [] => boundaryEntries col 0 rs
  | s::ss => boundaryEntries col 0 rs++registry (col+1) (s.render m rs).variableCount (s.render m rs).rails ss

theorem registry_initial (ss : List Stage) (col m : ℕ) (rs : List ℕ) (p : PortData)
    (hp : p∈boundaryEntries col 0 rs) : p∈registry col m rs ss := by
  cases ss with
  | nil => exact hp
  | cons s ss => exact List.mem_append_left _ hp

theorem registry_column_lower (ss : List Stage) (col m : ℕ) (rs : List ℕ) (p : PortData)
    (hp : p∈registry col m rs ss) : col≤p.2.1 := by
  induction ss generalizing col m rs with
  | nil => exact le_of_eq (boundaryEntries_position col 0 rs p hp).1.symm
  | cons s ss ih =>
    rcases List.mem_append.mp hp with hp | hp
    · exact le_of_eq (boundaryEntries_position col 0 rs p hp).1.symm
    · have h := ih (col+1) _ _ hp
      omega

theorem registry_ref_lower (ss : List Stage) (lo col m : ℕ) (rs : List ℕ)
    (hlm : lo≤m) (hlr : ∀x∈rs,lo≤x) (hr : ∀x∈rs,x<m) (hs : admissible m rs ss)
    (p : PortData) (hp : p∈registry col m rs ss) : lo≤p.1 := by
  induction ss generalizing col m rs with
  | nil => exact hlr _ (boundaryEntries_ref_mem col 0 rs p hp)
  | cons s ss ih =>
    rcases List.mem_append.mp hp with hp | hp
    · exact hlr _ (boundaryEntries_ref_mem col 0 rs p hp)
    · have hf := s.render_wellFormed m rs hr hs.1
      have hmg : m≤(s.render m rs).variableCount := (width_ge m _).trans_eq hf.width_eq
      exact ih (col+1) _ _ (hlm.trans hmg)
        (fun x hx => hlm.trans (s.render_lower m rs x hx)) hf.rails_valid hs.2 hp

/-- No numeric signal-variable name is reused at different stage boundaries. -/
theorem registry_refs_nodup (ss : List Stage) (col m : ℕ) (rs : List ℕ)
    (hr : ∀x∈rs,x<m) (hnd : rs.Nodup) (hs : admissible m rs ss) :
    ((registry col m rs ss).map Prod.fst).Nodup := by
  induction ss generalizing col m rs with
  | nil => simpa [registry] using hnd
  | cons s ss ih =>
    have hf := s.render_wellFormed m rs hr hs.1
    have hmg : m≤(s.render m rs).variableCount := (width_ge m _).trans_eq hf.width_eq
    simp only [registry,List.map_append,boundaryEntries_refs]
    apply List.nodup_append.mpr
    refine ⟨hnd,ih (col+1) _ _ hf.rails_valid (s.render_nodup m rs) hs.2,?_⟩
    intro x hx y hxt hxy
    subst y
    obtain ⟨p,hp,hpx⟩ := List.mem_map.mp hxt
    have hlow := registry_ref_lower ss m (col+1) (s.render m rs).variableCount (s.render m rs).rails hmg
      (fun x hx => s.render_lower m rs x hx) hf.rails_valid hs.2 p hp
    have hhigh := hr x hx
    omega

/-- No grid coordinate has two separately named signal variables. -/
theorem registry_positions_nodup (ss : List Stage) (col m : ℕ) (rs : List ℕ) :
    ((registry col m rs ss).map Prod.snd).Nodup := by
  induction ss generalizing col m rs with
  | nil => exact boundaryEntries_positions_nodup col 0 rs
  | cons s ss ih =>
    simp only [registry,List.map_append]
    apply List.nodup_append.mpr
    refine ⟨boundaryEntries_positions_nodup col 0 rs,ih (col+1) _ _,?_⟩
    intro pos hp pos' hq heq
    subst pos'
    obtain ⟨p,hp,hpp⟩ := List.mem_map.mp hp
    obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hq
    have hc := (boundaryEntries_position col 0 rs p hp).1
    have hd := registry_column_lower ss (col+1) _ _ q hq
    have hpos : p.2=q.2 := hpp.trans hqp.symm
    have he := congrArg Prod.fst hpos
    omega

/-- Every literal cell port occurs in the registry with exactly its emitted name. -/
theorem registry_ports (ss : List Stage) (col m : ℕ) (rs : List ℕ) (hs : admissible m rs ss)
    (c : Cell) (hc : c∈stagesCells col m rs ss) (k : Fin c.shape.portCount) :
    c.portData k∈registry col m rs ss := by
  induction ss generalizing col m rs with
  | nil => simp [stagesCells] at hc
  | cons s ss ih =>
    rcases List.mem_append.mp hc with hc | hc
    · have h := s.cells_ports col m rs hs.1 c hc k
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (registry_initial ss (col+1) _ _ _ h)
    · exact List.mem_append_right _ (ih (col+1) _ _ hs.2 hc)

/-- Registry names come only from original inputs or actual emitted output ports,
never from one of a cell's non-port auxiliary variables. -/
theorem registry_ref_source (ss : List Stage) (col m : ℕ) (rs : List ℕ)
    (p : PortData) (hp : p∈registry col m rs ss) :
    p.1∈rs ∨ p.1∈(stagesCells col m rs ss).flatMap Cell.outputRefs := by
  induction ss generalizing col m rs with
  | nil => exact Or.inl (boundaryEntries_ref_mem col 0 rs p hp)
  | cons s ss ih =>
    rcases List.mem_append.mp hp with hp | hp
    · exact Or.inl (boundaryEntries_ref_mem col 0 rs p hp)
    · have h := ih (col+1) _ _ hp
      right
      simp only [stagesCells,List.flatMap_append,List.mem_append]
      rcases h with h | h
      · left
        rwa [s.cells_outputs col m rs]
      · exact Or.inr h

def canvasRegistry (f : NumericFormula) : List PortData :=
  registry 0 f.1 (List.range f.1) (formulaStages f.1 f.2)

theorem canvasRegistry_refs_nodup (f : NumericFormula) (hf : NumericValid f) :
    ((canvasRegistry f).map Prod.fst).Nodup :=
  registry_refs_nodup _ _ _ _ (fun x hx => List.mem_range.mp hx) List.nodup_range
    (formulaStages_admissible _ _ _ _ (fun x hx => List.mem_range.mp hx) (by simp) hf)

theorem canvasRegistry_positions_nodup (f : NumericFormula) :
    ((canvasRegistry f).map Prod.snd).Nodup := registry_positions_nodup _ _ _ _

theorem canvasRegistry_port (f : NumericFormula) (hf : NumericValid f)
    (c : Cell) (hc : c∈canvas f) (k : Fin c.shape.portCount) : c.portData k∈canvasRegistry f := by
  have hs := formulaStages_admissible f.2 f.1 f.1 (List.range f.1)
    (fun x hx => List.mem_range.mp hx) (by simp) hf
  apply registry_ports _ _ _ _ hs c _ k
  simpa only [stagesCells_formulaStages] using hc

/-- The exact global gluing equivalence for every pair of actual emitted ports. -/
theorem canvas_port_name_iff_position (f : NumericFormula) (hf : NumericValid f)
    (c d : Cell) (hc : c∈canvas f) (hd : d∈canvas f)
    (i : Fin c.shape.portCount) (j : Fin d.shape.portCount) :
    (c.portData i).1=(d.portData j).1 ↔ (c.portData i).2=(d.portData j).2 := by
  have hp := canvasRegistry_port f hf c hc i
  have hq := canvasRegistry_port f hf d hd j
  constructor
  · intro h
    exact congrArg Prod.snd (List.inj_on_of_nodup_map (canvasRegistry_refs_nodup f hf) hp hq h)
  · intro h
    exact congrArg Prod.fst (List.inj_on_of_nodup_map (canvasRegistry_positions_nodup f) hp hq h)

end PlanarHom.PositiveBlockProgram
