import PlanarHom.CountingCookLevinReplayFold
import PlanarHom.CountingCookLevinBooleanTables

/-! Fixed-arity local kernel for the true tape-window transition. The local
context type depends only on the source machine, never on tape width or clock. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

set_option synthInstance.maxSize 4096
/-- Exactly the fixed finite data needed for any output register. -/
structure LocalContext (m : Machine) where
  control : Control m.Q
  head : m.Γ
  choice : Bool
  valid : Bool
  leftHead : Option m.Γ
  rightHead : Option m.Γ
  previous : Option m.Γ
  current : Option m.Γ
  next : Option m.Γ
  first : Bool
  leftSide : Bool
  deriving Fintype

def selectedAction (m : Machine) (q : Control m.Q) (head : m.Γ) (b : Bool) : Option (Action m.Γ m.Q) :=
  match q with
  | .accept | .reject => none
  | .run q => match m.transition q head with
    | .ordinary a => some a
    | .binary a d => some (if b then d else a)

def choiceAllowed (m : Machine) (q : Control m.Q) (head : m.Γ) (b : Bool) : Bool :=
  match q with
  | .accept => !b
  | .reject => false
  | .run q => match m.transition q head with
    | .ordinary _ => !b
    | .binary _ _ => true

def localControl (m : Machine) (c : LocalContext m) : Control m.Q :=
  ((selectedAction m c.control c.head c.choice).map Action.next).getD c.control

def localHead (m : Machine) (c : LocalContext m) : m.Γ :=
  match selectedAction m c.control c.head c.choice with
  | none => c.head
  | some a => match a.motion with
    | .stay => a.write
    | .left => c.leftHead.getD m.blank
    | .right => c.rightHead.getD m.blank

def localValid (m : Machine) (c : LocalContext m) : Bool :=
  c.valid && choiceAllowed m c.control c.head c.choice

def localCell (m : Machine) (c : LocalContext m) : Option m.Γ :=
  match selectedAction m c.control c.head c.choice with
  | none => c.current
  | some a => match a.motion with
    | .stay => c.current
    | .left => if c.leftSide then c.next else if c.first then some a.write else c.previous
    | .right => if c.leftSide then (if c.first then some a.write else c.previous) else c.next

def previousCell {A : Type} {L : ℕ} (v : Fin (L+1) → Option A) (i : Fin (L+1)) : Option A :=
  if h : 0 < i.val then v ⟨i.val-1,by omega⟩ else none

def nextCell {A : Type} {L : ℕ} (v : Fin (L+1) → Option A) (i : Fin (L+1)) : Option A :=
  if h : i.val+1 < L+1 then v ⟨i.val+1,h⟩ else none

theorem popWindow_eq_next {A : Type} {L : ℕ} (v : Fin (L+1) → Option A) (i : Fin (L+1)) :
    popWindow v i=nextCell v i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [popWindow,nextCell]
  · simp [popWindow,nextCell,j.isLt]
    rfl

theorem pushWindow_eq_previous {A : Type} {L : ℕ} (a : A) (v : Fin (L+1) → Option A) (i : Fin (L+1)) :
    pushWindow a v i=(if i.val=0 then some a else previousCell v i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pushWindow]
  · simp [pushWindow,previousCell]
    rfl

def contextAt (m : Machine) {L : ℕ} (s : ReplayState m L) (b side : Bool) (i : Fin (L+1)) : LocalContext m where
  control := s.1.1.1
  head := s.1.1.2
  choice := b
  valid := s.2
  leftHead := s.1.2.1 0
  rightHead := s.1.2.2 0
  previous := previousCell (if side then s.1.2.1 else s.1.2.2) i
  current := (if side then s.1.2.1 else s.1.2.2) i
  next := nextCell (if side then s.1.2.1 else s.1.2.2) i
  first := decide (i.val=0)
  leftSide := side

/-- All control/head/validity outputs depend on fixed finite local data. -/
theorem windowStep_local_controls (m : Machine) {L : ℕ} (s : ReplayState m L)
    (b side : Bool) (i : Fin (L+1)) :
    localControl m (contextAt m s b side i)=(windowStep m s b).1.1.1 ∧
    localHead m (contextAt m s b side i)=(windowStep m s b).1.1.2 ∧
    localValid m (contextAt m s b side i)=(windowStep m s b).2 := by
  rcases s with ⟨⟨⟨q,head⟩,left,right⟩,ok⟩
  cases q with
  | accept => simp [localControl,localHead,localValid,selectedAction,choiceAllowed,contextAt,windowStep]
  | reject => simp [localControl,localHead,localValid,selectedAction,choiceAllowed,contextAt,windowStep]
  | run q =>
    cases h : m.transition q head with
    | ordinary a =>
      cases hm : a.motion <;> simp [localControl,localHead,localValid,selectedAction,choiceAllowed,
        contextAt,windowStep,h,windowAction,hm]
    | binary a d =>
      cases b
      · cases hm : a.motion <;> simp [localControl,localHead,localValid,selectedAction,choiceAllowed,
          contextAt,windowStep,h,windowAction,hm]
      · cases hm : d.motion <;> simp [localControl,localHead,localValid,selectedAction,choiceAllowed,
          contextAt,windowStep,h,windowAction,hm]

/-- Every tape output cell is the same fixed finite function of at most eleven
local fields. No global-state truth table or width-dependent arity is used. -/
theorem windowStep_local_cell (m : Machine) {L : ℕ} (s : ReplayState m L)
    (b side : Bool) (i : Fin (L+1)) :
    localCell m (contextAt m s b side i)=
      (if side then (windowStep m s b).1.2.1 else (windowStep m s b).1.2.2) i := by
  rcases s with ⟨⟨⟨q,head⟩,left,right⟩,ok⟩
  cases q with
  | accept => simp [localCell,selectedAction,contextAt,windowStep]
  | reject => simp [localCell,selectedAction,contextAt,windowStep]
  | run q =>
    cases h : m.transition q head with
    | ordinary a =>
      cases hm : a.motion <;> cases side <;>
        simp [localCell,selectedAction,contextAt,windowStep,h,windowAction,hm,
          popWindow_eq_next,pushWindow_eq_previous]
    | binary a d =>
      cases b
      · cases hm : a.motion <;> cases side <;>
          simp [localCell,selectedAction,contextAt,windowStep,h,windowAction,hm,
            popWindow_eq_next,pushWindow_eq_previous]
      · cases hm : d.motion <;> cases side <;>
          simp [localCell,selectedAction,contextAt,windowStep,h,windowAction,hm,
            popWindow_eq_next,pushWindow_eq_previous]

end PlanarHom.CountingCookLevin
