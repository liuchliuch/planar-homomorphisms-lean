import PlanarHom.OccurrenceKasteleynPeelingSemantics

/-!
# NEW proof: exact forward-loop and reverse-repair orientation implementation

The finite face solver is implemented by a bounded forward pivot loop storing a
reverse-order stack, followed by a left fold repairing its rows. The result is
proved equal, unconditionally on every raw table, to `computeOrientation`.
No face validity, peelability, or planarity premise substitutes for that program
equality. This is the algebraic interface for the separate encoded FP compiler.
-/
namespace PlanarHom.MultiGraph.Kasteleyn

abbrev RawPivot := Nat × Nat
abbrev OrientationState := List RawFace × (List Nat × List RawPivot)

/-- Table stays fixed. A successful pivot removes one face label and pushes the
literal face/edge pair; failure clears the residual list and retains the stack. -/
def peelStep (state : OrientationState) : OrientationState :=
  match pickPivot (tableBoundary state.1) state.2.1 with
  | none => (state.1,([],state.2.2))
  | some p => (state.1,(state.2.1.erase p.1,p::state.2.2))

def initialOrientationState (table : List RawFace) : OrientationState :=
  (table,(table.map Prod.fst,[]))

def peelState (table : List RawFace) : OrientationState :=
  peelStep^[table.length] (initialOrientationState table)

/-- Reverse substitution stores a toggle iff the current row is unsatisfied. -/
def repairLog (table : List RawFace) (log : List Nat) (p : RawPivot) : List Nat :=
  if boundaryParity (logOrientation log) (tableBoundary table p.1) =
      faceTarget (tableBoundary table p.1)
  then log else p.2::log

/-- Entire actual forward-loop/fold implementation under the original raw types. -/
def computeOrientationIterative (table : List RawFace) : List Nat :=
  (peelState table).2.2.foldl (repairLog table) []

/-- Semantic chronological trace of exactly the pivots selected by the loop. -/
def pivotTrace (boundary : Boundaries Nat Nat) : Nat → List Nat → List RawPivot
  | 0, _ => []
  | n+1, fs =>
    match pickPivot boundary fs with
    | none => []
    | some p => p :: pivotTrace boundary n (fs.erase p.1)

@[simp] theorem pivotTrace_empty (boundary : Boundaries Nat Nat) (n : Nat) :
    pivotTrace boundary n [] = [] := by
  cases n <;> simp [pivotTrace,pickPivot,pivotCandidates]

/-- Exact stack state after any number of forward steps, with any initial prefix. -/
theorem peelStep_iterate_stack (table : List RawFace) (n : Nat)
    (fs : List Nat) (stack : List RawPivot) :
    (peelStep^[n] (table,(fs,stack))).2.2 =
      (pivotTrace (tableBoundary table) n fs).reverse ++ stack := by
  induction n generalizing fs stack with
  | zero => simp [pivotTrace]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases hp : pickPivot (tableBoundary table) fs with
    | none =>
      simp only [peelStep,hp,pivotTrace,ih,pivotTrace_empty,List.reverse_nil,List.nil_append]
    | some p =>
      simp only [peelStep,hp,pivotTrace,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

/-- The reverse repair recursion is exactly a right fold of the chronological
trace; this statement holds for arbitrary, including malformed, raw inputs. -/
theorem orientLogAux_eq_foldr (table : List RawFace) (n : Nat) (fs : List Nat) :
    orientLogAux (tableBoundary table) n fs =
      (pivotTrace (tableBoundary table) n fs).foldr (fun p log => repairLog table log p) [] := by
  induction n generalizing fs with
  | zero => rfl
  | succ n ih =>
    cases hp : pickPivot (tableBoundary table) fs with
    | none => simp [orientLogAux,pivotTrace,hp]
    | some p => simp [orientLogAux,pivotTrace,hp,repairLog,ih]

/-- The finite iteration/fold program computes exactly the previously proved
face solver, not merely another orientation satisfying the same equations. -/
theorem computeOrientationIterative_eq_computeOrientation (table : List RawFace) :
    computeOrientationIterative table = computeOrientation table := by
  unfold computeOrientationIterative peelState initialOrientationState computeOrientation
  rw [peelStep_iterate_stack,List.append_nil,orientLogAux_eq_foldr]
  exact List.foldl_reverse


/-- Every trace consumes at most its fuel, even for malformed tables. -/
theorem pivotTrace_length_le_fuel (boundary : Boundaries Nat Nat) (n : Nat) (fs : List Nat) :
    (pivotTrace boundary n fs).length ≤ n := by
  induction n generalizing fs with
  | zero => simp [pivotTrace]
  | succ n ih =>
    cases hp : pickPivot boundary fs with
    | none => simp [pivotTrace,hp]
    | some p => simpa [pivotTrace,hp] using Nat.succ_le_succ (ih (fs.erase p.1))

/-- A successful step really removes one occurrence from the residual face list. -/
theorem pivotTrace_length_le_faces (boundary : Boundaries Nat Nat) (n : Nat) (fs : List Nat) :
    (pivotTrace boundary n fs).length ≤ fs.length := by
  induction n generalizing fs with
  | zero => simp [pivotTrace]
  | succ n ih =>
    cases hp : pickPivot boundary fs with
    | none => simp [pivotTrace,hp]
    | some p =>
      have hmem := (pickPivot_sound boundary fs hp).1
      have hlen := ih (fs.erase p.1)
      rw [List.length_erase_of_mem hmem] at hlen
      have hpos : 0 < fs.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
      simp only [pivotTrace,hp,List.length_cons]
      omega

/-- Every stored face label came from the input residual list. -/
theorem pivotTrace_face_mem (boundary : Boundaries Nat Nat) (n : Nat) (fs : List Nat)
    {p : RawPivot} (hp : p ∈ pivotTrace boundary n fs) : p.1 ∈ fs := by
  induction n generalizing fs with
  | zero => simp [pivotTrace] at hp
  | succ n ih =>
    cases h : pickPivot boundary fs with
    | none => simp [pivotTrace,h] at hp
    | some q =>
      simp only [pivotTrace,h,List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact (pickPivot_sound boundary fs h).1
      · exact List.erase_subset (ih _ hp)

/-- Every stored pivot is a literal dart index in its selected boundary row. -/
theorem pivotTrace_edge_mem (boundary : Boundaries Nat Nat) (n : Nat) (fs : List Nat)
    {p : RawPivot} (hp : p ∈ pivotTrace boundary n fs) :
    ∃ a ∈ boundary p.1, a.1=p.2 := by
  induction n generalizing fs with
  | zero => simp [pivotTrace] at hp
  | succ n ih =>
    cases h : pickPivot boundary fs with
    | none => simp [pivotTrace,h] at hp
    | some q =>
      simp only [pivotTrace,h,List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact exists_dart_of_incidenceParity (pickPivot_sound boundary fs h).2.1
      · exact ih _ hp

/-- The table is immutable throughout every prefix of the bounded loop. -/
theorem peelStep_iterate_table (table : List RawFace) (n : Nat)
    (fs : List Nat) (stack : List RawPivot) :
    (peelStep^[n] (table,(fs,stack))).1 = table := by
  induction n generalizing fs stack with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases h : pickPivot (tableBoundary table) fs <;> simp only [peelStep,h,ih]

/-- Every residual list is a sublist of the initial materialized face labels. -/
theorem peelStep_iterate_faces_sublist (table : List RawFace) (n : Nat)
    (fs : List Nat) (stack : List RawPivot) :
    (peelStep^[n] (table,(fs,stack))).2.1.Sublist fs := by
  induction n generalizing fs stack with
  | zero => exact List.Sublist.refl fs
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases h : pickPivot (tableBoundary table) fs with
    | none =>
      simp only [peelStep,h]
      exact (ih [] stack).trans (List.nil_sublist fs)
    | some p =>
      simp only [peelStep,h]
      exact (ih (fs.erase p.1) (p::stack)).trans List.erase_sublist

theorem peelStep_iterate_stack_length (table : List RawFace) (n : Nat)
    (fs : List Nat) (stack : List RawPivot) :
    (peelStep^[n] (table,(fs,stack))).2.2.length ≤ n+stack.length := by
  rw [peelStep_iterate_stack,List.length_append,List.length_reverse]
  exact Nat.add_le_add_right (pivotTrace_length_le_fuel _ _ _) _

/-- A retrieved boundary contains only darts of an actual original table row. -/
theorem tableBoundary_mem_source (table : List RawFace) (f : Nat)
    {a : Dart Nat} (ha : a ∈ tableBoundary table f) :
    ∃ ds, (f,ds) ∈ table ∧ a ∈ ds := by
  unfold tableBoundary at ha
  cases h : table.lookup f with
  | none => simp [h] at ha
  | some ds =>
    have hamem : a ∈ ds := by simpa [h] using ha
    obtain ⟨xs,ys,ht,_⟩ := List.lookup_eq_some_iff.mp h
    exact ⟨ds,ht ▸ (by simp),hamem⟩

/-- Raw member invariant used to bound the bit size of both stored pivot fields. -/
theorem peelState_stack_mem_source (table : List RawFace) {p : RawPivot}
    (hp : p ∈ (peelState table).2.2) :
    ∃ ds, (p.1,ds) ∈ table ∧ ∃ a ∈ ds, a.1=p.2 := by
  have htrace : p ∈ pivotTrace (tableBoundary table) table.length (table.map Prod.fst) := by
    simpa only [peelState,initialOrientationState,peelStep_iterate_stack,
      List.append_nil,List.mem_reverse] using hp
  obtain ⟨a,ha,hae⟩ := pivotTrace_edge_mem _ _ _ htrace
  obtain ⟨ds,hds,hads⟩ := tableBoundary_mem_source table p.1 ha
  exact ⟨ds,hds,a,hads,hae⟩

/-- The reverse-repair fold can add at most one edge index per stored pivot. -/
theorem repairLog_foldl_length (table : List RawFace) (stack : List RawPivot) (log : List Nat) :
    (stack.foldl (repairLog table) log).length ≤ log.length+stack.length := by
  induction stack generalizing log with
  | nil => simp
  | cons p stack ih =>
    rw [List.foldl_cons]
    have h := ih (repairLog table log p)
    have hstep : (repairLog table log p).length ≤ log.length+1 := by
      unfold repairLog
      split_ifs <;> simp
    simp only [List.length_cons]
    omega

/-- Each returned index came from the initial log or from one literal pivot. -/
theorem repairLog_foldl_mem (table : List RawFace) (stack : List RawPivot) (log : List Nat)
    {e : Nat} (he : e ∈ stack.foldl (repairLog table) log) :
    e ∈ log ∨ ∃ p ∈ stack, p.2=e := by
  induction stack generalizing log with
  | nil => exact Or.inl he
  | cons p stack ih =>
    rw [List.foldl_cons] at he
    rcases ih _ he with hlog | ⟨q,hq,hqe⟩
    · unfold repairLog at hlog
      split_ifs at hlog
      · exact Or.inl hlog
      · rcases List.mem_cons.mp hlog with heq | hlog
        · exact Or.inr ⟨p,List.mem_cons_self,heq.symm⟩
        · exact Or.inl hlog
    · exact Or.inr ⟨q,List.mem_cons_of_mem _ hq,hqe⟩

/-- Unconditional total output-length bound, with no valid-face-table premise. -/
theorem computeOrientation_length_le (table : List RawFace) :
    (computeOrientation table).length ≤ table.length := by
  rw [← computeOrientationIterative_eq_computeOrientation]
  have h := repairLog_foldl_length table (peelState table).2.2 []
  have hs := peelStep_iterate_stack_length table table.length (table.map Prod.fst) []
  simpa only [computeOrientationIterative,peelState,initialOrientationState,
    List.length_nil,Nat.zero_add,Nat.add_zero] using h.trans (by simpa only [List.length_nil,Nat.zero_add,Nat.add_zero] using hs)

/-- Output indices are copied from original input darts; their numeric word sizes
cannot grow through arithmetic or fabricated labels. -/
theorem computeOrientation_mem_source (table : List RawFace) {e : Nat}
    (he : e ∈ computeOrientation table) :
    ∃ f ds, (f,ds) ∈ table ∧ ∃ a ∈ ds, a.1=e := by
  rw [← computeOrientationIterative_eq_computeOrientation] at he
  rcases repairLog_foldl_mem table (peelState table).2.2 [] he with h | ⟨p,hp,hpe⟩
  · simp at h
  · obtain ⟨ds,hds,a,ha,hae⟩ := peelState_stack_mem_source table hp
    exact ⟨p.1,ds,hds,a,ha,hae.trans hpe⟩


/-- Literal payload bound: repair copies a sublist of the reverse pivot indices
followed by the initial log, without duplicating or fabricating stored values. -/
theorem repairLog_foldl_sublist (table : List RawFace) (stack : List RawPivot) (log : List Nat) :
    (stack.foldl (repairLog table) log).Sublist ((stack.map Prod.snd).reverse ++ log) := by
  induction stack generalizing log with
  | nil => simp
  | cons p stack ih =>
    rw [List.foldl_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    have hstep : (repairLog table log p).Sublist (p.2::log) := by
      unfold repairLog
      split_ifs
      · exact List.sublist_cons_self _ _
      · exact List.Sublist.refl _
    exact (ih _).trans (hstep.append_left _)

/-- Every intermediate stack entry is retained from the original stack or
copied from an actual row/dart of the unchanged table. -/
theorem peelStep_iterate_stack_mem_source (table : List RawFace) (n : Nat)
    (fs : List Nat) (stack : List RawPivot) {p : RawPivot}
    (hp : p ∈ (peelStep^[n] (table,(fs,stack))).2.2) :
    p ∈ stack ∨ ∃ ds, (p.1,ds) ∈ table ∧ ∃ a ∈ ds, a.1=p.2 := by
  rw [peelStep_iterate_stack,List.mem_append,List.mem_reverse] at hp
  rcases hp with hp | hp
  · obtain ⟨a,ha,hae⟩ := pivotTrace_edge_mem _ _ _ hp
    obtain ⟨ds,hds,hads⟩ := tableBoundary_mem_source table p.1 ha
    exact Or.inr ⟨ds,hds,a,hads,hae⟩
  · exact Or.inl hp

/-- A face label is copied from the original residual list or stack. -/
theorem peelStep_iterate_stack_face_mem (table : List RawFace) (n : Nat)
    (fs : List Nat) (stack : List RawPivot) {p : RawPivot}
    (hp : p ∈ (peelStep^[n] (table,(fs,stack))).2.2) :
    p ∈ stack ∨ p.1 ∈ fs := by
  rw [peelStep_iterate_stack,List.mem_append,List.mem_reverse] at hp
  exact hp.elim (fun h => Or.inr (pivotTrace_face_mem _ _ _ h)) Or.inl

end PlanarHom.MultiGraph.Kasteleyn
