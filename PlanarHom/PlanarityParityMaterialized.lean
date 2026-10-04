import PlanarHom.PlanarityParitySolver

/-! NEW bounded-list forward elimination and backward substitution. This
materialized program is designed for the existing typed FP fold compiler. -/
namespace PlanarHom.PlanarityParitySolver

abbrev ForwardState := (List Constraint × List Constraint) × Bool

def backStep (xs : Assignment) (e : Constraint) : Assignment :=
  (e.1,Bool.xor (lookup xs e.2.1) e.2.2)::xs

def replay (log : List Constraint) : Assignment := log.foldl backStep []

/-- Materialized residual equations and reverse elimination log. -/
def forwardStep (s : ForwardState) (_ : Constraint) : ForwardState :=
  match s.1.1 with
  | [] => s
  | (u,v,b)::tail =>
    if u = v then ((tail,s.1.2),s.2 && !b)
    else ((tail.map (substitute u v b),(u,v,b)::s.1.2),s.2)

/-- Reference semantics of the elimination log. -/
def eliminationLog (es : List Constraint) : Bool × List Constraint :=
  match es with
  | [] => (true,[])
  | (u,v,b)::tail =>
    if u = v then
      let r := eliminationLog tail
      (r.1 && !b,r.2)
    else
      let r := eliminationLog (tail.map (substitute u v b))
      (r.1,r.2++[(u,v,b)])
termination_by es.length

/-- The list-state algorithm iterates exactly once per original equation. -/
def forwardRun (es : List Constraint) : ForwardState :=
  es.foldl forwardStep ((es,[]),true)

def computed (es : List Constraint) : Bool × Assignment :=
  let s := forwardRun es
  (s.2,replay s.1.2)

theorem fold_empty_state (ticks : List Constraint) (log : List Constraint) (ok : Bool) :
    ticks.foldl forwardStep (([],log),ok) = (([],log),ok) := by
  induction ticks with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons,forwardStep] using ih

/-- Literal bounded-list execution agrees with recursive elimination-log semantics. -/
theorem fold_forward_eq (es ticks log : List Constraint) (ok : Bool)
    (hlen : es.length ≤ ticks.length) :
    ticks.foldl forwardStep ((es,log),ok) =
      (([],(eliminationLog es).2 ++ log),ok && (eliminationLog es).1) := by
  cases es with
  | nil => simp [eliminationLog,fold_empty_state]
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    cases ticks with
    | nil => simp at hlen
    | cons x ticks =>
      have hlen' : tail.length ≤ ticks.length := by simpa using hlen
      by_cases he : u = v
      · rw [List.foldl_cons]
        simp only [forwardStep,if_pos he]
        rw [fold_forward_eq tail ticks log (ok && !b) hlen']
        simp [eliminationLog,he,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]
      · rw [List.foldl_cons]
        simp only [forwardStep,if_neg he]
        rw [fold_forward_eq (tail.map (substitute u v b)) ticks ((u,v,b)::log) ok
          (by simpa using hlen')]
        simp [eliminationLog,he,List.append_assoc]
termination_by es.length

theorem forwardRun_eq (es : List Constraint) :
    forwardRun es = (([],(eliminationLog es).2),(eliminationLog es).1) := by
  simpa [forwardRun] using fold_forward_eq es es [] true le_rfl

/-- Backward substitution reproduces the original solver exactly. -/
theorem solve_eq_eliminationLog (es : List Constraint) :
    solve es = if (eliminationLog es).1 then some (replay (eliminationLog es).2) else none := by
  cases es with
  | nil => simp [solve,eliminationLog,replay]
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    by_cases he : u = v
    · cases b
      · simpa [solve,eliminationLog,he] using solve_eq_eliminationLog tail
      · simp [solve,eliminationLog,he]
    · rw [solve]
      simp only [if_neg he]
      rw [solve_eq_eliminationLog (tail.map (substitute u v b))]
      simp only [eliminationLog,if_neg he]
      split <;> simp_all [replay,List.foldl_append,backStep]
termination_by es.length

/-- The entirely materialized bounded-fold output carries the same success flag
and assignment as the exact recursive solver. -/
theorem computed_result (es : List Constraint) :
    (if (computed es).1 then some (computed es).2 else none) = solve es := by
  rw [solve_eq_eliminationLog]
  simp [computed,forwardRun_eq]

theorem computed_sound (es : List Constraint) (h : (computed es).1 = true) :
    Satisfies (lookup (computed es).2) es := by
  apply solve_sound
  rw [← computed_result,h]
  rfl

theorem computed_complete (es : List Constraint) :
    (computed es).1 = true ↔ ∃ f, Satisfies f es := by
  rw [← solve_success_iff,← computed_result]
  cases h : (computed es).1 <;> simp

end PlanarHom.PlanarityParitySolver
