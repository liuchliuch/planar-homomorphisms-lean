import PlanarHom.GraphComponentMachines

/-!
# NEW executable parity-constraint elimination for LR planarity

This module computes Boolean left/right assignments for finite binary parity
constraints. It does not assume a satisfying assignment. Translating ordinary
planarity to the actual LR constraint family, producing a valid planar rotation,
and realizing that rotation geometrically are separate obligations.
-/
namespace PlanarHom.PlanarityParitySolver

abbrev Constraint := ℕ × (ℕ × Bool)
abbrev Assignment := List (ℕ × Bool)

def lookup : Assignment → ℕ → Bool
  | [], _ => false
  | (u,b)::xs, v => if v = u then b else lookup xs v

def Holds (f : ℕ → Bool) (e : Constraint) : Prop := Bool.xor (f e.1) (f e.2.1) = e.2.2

def Satisfies (f : ℕ → Bool) (es : List Constraint) : Prop := ∀ e ∈ es, Holds f e

/-- Substitute `u = v xor b` in one literal binary parity equation. -/
def substitute (u v : ℕ) (b : Bool) (e : Constraint) : Constraint :=
  (if e.1 = u then v else e.1,
    if e.2.1 = u then v else e.2.1,
    Bool.xor (Bool.xor e.2.2 (if e.1 = u then b else false))
      (if e.2.1 = u then b else false))

def extend (f : ℕ → Bool) (u v : ℕ) (b : Bool) : ℕ → Bool :=
  fun x => if x = u then Bool.xor (f v) b else f x

/-- One actual eliminating substitution, with no satisfiability premise. -/
theorem holds_extend_iff (f : ℕ → Bool) {u v : ℕ} (huv : u ≠ v) (b : Bool) (e : Constraint) :
    Holds (extend f u v b) e ↔ Holds f (substitute u v b e) := by
  rcases e with ⟨x,y,t⟩
  by_cases hx : x = u <;> by_cases hy : y = u <;>
    simp only [Holds,extend,substitute,hx,hy,if_true,if_false,Prod.fst,Prod.snd]
  all_goals cases b <;> cases t <;> cases f v <;> cases f x <;> cases f y <;> decide

/-- The eliminated equation itself is satisfied after extension. -/
theorem holds_extend_pivot (f : ℕ → Bool) {u v : ℕ} (huv : u ≠ v) (b : Bool) :
    Holds (extend f u v b) (u,v,b) := by
  simp only [Holds,extend,if_pos rfl,if_neg huv.symm]
  cases b <;> cases f v <;> rfl

/-- A previously satisfying assignment is unchanged by its own elimination. -/
theorem extend_eq_self (f : ℕ → Bool) {u v : ℕ} (b : Bool)
    (h : Holds f (u,v,b)) : extend f u v b = f := by
  funext x
  by_cases hx : x = u
  · subst x
    simp only [extend,if_pos rfl]
    unfold Holds at h
    cases hfu : f u <;> cases hfv : f v <;> cases b <;> simp_all
  · simp [extend,hx]

/-- Recursive elimination computes an explicit assignment or detects a contradictory
self equation. Each branch removes the current head before recurring. -/
def solve (es : List Constraint) : Option Assignment :=
  match es with
  | [] => some []
  | (u,v,b)::tail =>
    if u = v then
      if b then none else solve tail
    else (solve (tail.map (substitute u v b))).map
      (fun xs => (u,Bool.xor (lookup xs v) b)::xs)
termination_by es.length

@[simp] theorem solve_nil : solve [] = some [] := by simp [solve]

theorem lookup_cons_extend (xs : Assignment) (u v : ℕ) (b : Bool) :
    lookup ((u,Bool.xor (lookup xs v) b)::xs) = extend (lookup xs) u v b := rfl

/-- Successful output satisfies every input equation, including repeated labels. -/
theorem solve_sound (es : List Constraint) (xs : Assignment) (h : solve es = some xs) :
    Satisfies (lookup xs) es := by
  cases es with
  | nil => simp [Satisfies]
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    by_cases he : u = v
    · by_cases hb : b = true
      · simp [solve,he,hb] at h
      · have hs : solve tail = some xs := by simpa [solve,he,hb] using h
        have ht := solve_sound tail xs hs
        intro e hem
        rcases List.mem_cons.mp hem with rfl | hem
        · subst v
          cases b <;> simp_all [Holds]
        · exact ht e hem
    · have hs : (solve (tail.map (substitute u v b))).map
          (fun ys => (u,Bool.xor (lookup ys v) b)::ys) = some xs := by
        simpa only [solve,if_neg he] using h
      obtain ⟨ys,hys,rfl⟩ := Option.map_eq_some_iff.mp hs
      have ht := solve_sound (tail.map (substitute u v b)) ys hys
      rw [lookup_cons_extend]
      intro e hem
      rcases List.mem_cons.mp hem with rfl | hem
      · exact holds_extend_pivot _ he b
      · exact (holds_extend_iff _ he b e).mpr (ht _ (List.mem_map.mpr ⟨e,hem,rfl⟩))
termination_by es.length

/-- Every satisfiable input produces a concrete successful assignment. -/
theorem solve_complete (es : List Constraint) (f : ℕ → Bool) (hf : Satisfies f es) :
    ∃ xs, solve es = some xs := by
  cases es with
  | nil => exact ⟨[],solve_nil⟩
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    have hp := hf (u,v,b) (List.mem_cons_self ..)
    have ht : Satisfies f tail := fun e he => hf e (List.mem_cons_of_mem _ he)
    by_cases he : u = v
    · have hb : b = false := by subst v; simpa [Holds] using hp.symm
      obtain ⟨xs,hxs⟩ := solve_complete tail f ht
      exact ⟨xs,by simpa [solve,he,hb] using hxs⟩
    · have hsubst : Satisfies f (tail.map (substitute u v b)) := by
        intro e hem
        obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hem
        apply (holds_extend_iff f he b c).mp
        rw [extend_eq_self f b hp]
        exact ht c hc
      obtain ⟨xs,hxs⟩ := solve_complete (tail.map (substitute u v b)) f hsubst
      refine ⟨(u,Bool.xor (lookup xs v) b)::xs,?_⟩
      simp only [solve,if_neg he,hxs,Option.map_some]
termination_by es.length

/-- Exact total decision specification: no oracle or proposed assignment is input. -/
theorem solve_success_iff (es : List Constraint) :
    (∃ xs, solve es = some xs) ↔ ∃ f, Satisfies f es := by
  constructor
  · rintro ⟨xs,h⟩
    exact ⟨lookup xs,solve_sound es xs h⟩
  · rintro ⟨f,h⟩
    exact solve_complete es f h



/-- Elimination emits at most one explicit assignment binding per equation. -/
theorem solve_length (es : List Constraint) (xs : Assignment) (h : solve es = some xs) :
    xs.length ≤ es.length := by
  cases es with
  | nil => simpa [solve] using h.symm
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    by_cases he : u = v
    · by_cases hb : b = true
      · simp [solve,he,hb] at h
      · have hs : solve tail = some xs := by simpa [solve,he,hb] using h
        exact (solve_length tail xs hs).trans (by simp)
    · have hs : (solve (tail.map (substitute u v b))).map
          (fun ys => (u,Bool.xor (lookup ys v) b)::ys) = some xs := by
        simpa only [solve,if_neg he] using h
      obtain ⟨ys,hys,rfl⟩ := Option.map_eq_some_iff.mp hs
      have ht := solve_length (tail.map (substitute u v b)) ys hys
      simpa only [List.length_cons,List.length_map] using
        Nat.succ_le_succ ht
termination_by es.length

/-- Every emitted label remains within any input label bound. -/
theorem solve_labels (es : List Constraint) (xs : Assignment) (h : solve es = some xs)
    (B : ℕ) (hB : ∀ e ∈ es, e.1 < B ∧ e.2.1 < B) : ∀ p ∈ xs, p.1 < B := by
  cases es with
  | nil => simp [solve] at h; subst xs; simp
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    have huv := hB (u,v,b) (List.mem_cons_self ..)
    by_cases he : u = v
    · by_cases hb : b = true
      · simp [solve,he,hb] at h
      · have hs : solve tail = some xs := by simpa [solve,he,hb] using h
        exact solve_labels tail xs hs B (fun e he => hB e (List.mem_cons_of_mem _ he))
    · have hs : (solve (tail.map (substitute u v b))).map
          (fun ys => (u,Bool.xor (lookup ys v) b)::ys) = some xs := by
        simpa only [solve,if_neg he] using h
      obtain ⟨ys,hys,rfl⟩ := Option.map_eq_some_iff.mp hs
      have ht := solve_labels (tail.map (substitute u v b)) ys hys B (by
        intro e hem
        obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hem
        have hcB := hB c (List.mem_cons_of_mem _ hc)
        simp only [substitute]
        constructor
        · split_ifs <;> first | exact huv.2 | exact hcB.1
        · split_ifs <;> first | exact huv.2 | exact hcB.2)
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact huv.1
      · exact ht p hp
termination_by es.length

/-- Literal lookup comparisons, charging its final empty-list case. -/
def lookupWork : Assignment → ℕ → ℕ
  | [], _ => 1
  | (u,_)::xs, v => if v = u then 1 else 1 + lookupWork xs v

theorem lookupWork_bound (xs : Assignment) (v : ℕ) : lookupWork xs v ≤ xs.length+1 := by
  induction xs with
  | nil => simp [lookupWork]
  | cons p xs ih => rcases p with ⟨u,b⟩; simp only [lookupWork,List.length_cons]; split_ifs <;> omega

/-- The same executable elimination with explicit work accounting. Substitution
charges five elementary comparisons/XOR/list operations per remaining equation;
natural-label comparisons are unit cost here, not a bit-complexity claim. -/
def solveWithWork (es : List Constraint) : Option Assignment × ℕ :=
  match es with
  | [] => (some [],1)
  | (u,v,b)::tail =>
    if u = v then
      if b then (none,2) else
        let result := solveWithWork tail
        (result.1,result.2+2)
    else
      let result := solveWithWork (tail.map (substitute u v b))
      match result.1 with
      | none => (none,result.2+5*tail.length+3)
      | some xs => (some ((u,Bool.xor (lookup xs v) b)::xs),
          result.2+5*tail.length+lookupWork xs v+4)
termination_by es.length

/-- The instrumented algorithm returns exactly the already-verified solver output. -/
theorem solveWithWork_result (es : List Constraint) : (solveWithWork es).1 = solve es := by
  cases es with
  | nil => simp [solveWithWork,solve]
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    by_cases he : u = v
    · by_cases hb : b = true
      · simp [solveWithWork,solve,he,hb]
      · simp only [solveWithWork,solve,he,if_true,hb,Bool.false_eq_true,if_false]
        exact solveWithWork_result tail
    · have ih := solveWithWork_result (tail.map (substitute u v b))
      simp only [solveWithWork,solve,if_neg he]
      rw [← ih]
      cases (solveWithWork (tail.map (substitute u v b))).1 <;> rfl
termination_by es.length

/-- Quadratic number of actual substitution/lookup operations, independent of
whether the system is satisfiable. -/
theorem solveWithWork_bound (es : List Constraint) :
    (solveWithWork es).2 ≤ 6*(es.length+1)^2 := by
  cases es with
  | nil => norm_num [solveWithWork]
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    by_cases he : u = v
    · by_cases hb : b = true
      · simp only [solveWithWork,he,if_true,hb,List.length_cons]
        nlinarith [Nat.zero_le tail.length]
      · have ih := solveWithWork_bound tail
        simp only [solveWithWork,he,if_true,hb,Bool.false_eq_true,if_false,List.length_cons]
        nlinarith [Nat.zero_le tail.length]
    · have ih := solveWithWork_bound (tail.map (substitute u v b))
      simp only [List.length_map] at ih
      simp only [solveWithWork,if_neg he,List.length_cons]
      split
      · dsimp
        nlinarith [Nat.zero_le tail.length]
      · rename_i xs hxs
        have hs : solve (tail.map (substitute u v b)) = some xs := by
          rw [← solveWithWork_result]
          exact hxs
        have hl := solve_length _ _ hs
        simp only [List.length_map] at hl
        have hw := lookupWork_bound xs v
        dsimp
        nlinarith [Nat.zero_le tail.length]
termination_by es.length

end PlanarHom.PlanarityParitySolver
