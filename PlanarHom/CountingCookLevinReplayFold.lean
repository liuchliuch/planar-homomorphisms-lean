import PlanarHom.CountingCookLevinTapeWindow

/-! The fixed-width replay predicate is an actual iteration of one local
finite-state kernel, rather than an exponentially unfolded computation tree. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic NondeterministicComputationTree

/-- A Boolean flag records whether the consumed choices respect canonical
ordinary and post-halt padding. -/
abbrev ReplayState (m : Machine) (L : ℕ) := Window m L × Bool

def acceptingWindow (m : Machine) {L : ℕ} (c : Window m L) : Bool :=
  match c.1.1 with | .accept => true | _ => false

def windowStep (m : Machine) {L : ℕ} (s : ReplayState m L) (b : Bool) : ReplayState m L :=
  match s.1.1.1 with
  | .accept => (s.1,s.2 && !b)
  | .reject => (s.1,false)
  | .run q => match m.transition q s.1.1.2 with
    | .ordinary a => (windowAction m a s.1,s.2 && !b)
    | .binary a d => (windowAction m (if b then d else a) s.1,s.2)

def finalBit (m : Machine) {L : ℕ} (s : ReplayState m L) : Bool :=
  s.2 && acceptingWindow m s.1

/-- Exact fold specification retains all false-padding checks, and works even
for states whose validity flag was already false. -/
theorem fold_windowStep (m : Machine) {L : ℕ} (s : ReplayState m L) (bs : List Bool) :
    finalBit m (bs.foldl (windowStep m) s)= (s.2 && replay (windowView m) s.1 bs) := by
  induction bs generalizing s with
  | nil =>
    rcases s with ⟨⟨⟨q,h⟩,left,right⟩,ok⟩
    cases q with
    | accept => rfl
    | reject => simp [finalBit,acceptingWindow,replay,windowView]
    | run q =>
      cases hs : m.transition q h <;> simp [finalBit,acceptingWindow,replay,windowView,hs]
  | cons b bs ih =>
    rw [List.foldl_cons,ih]
    rcases s with ⟨⟨⟨q,h⟩,left,right⟩,ok⟩
    cases q with
    | accept =>
      simp [windowStep,replay,windowView,Bool.and_assoc]
    | reject => simp [windowStep,replay,windowView]
    | run q =>
      cases hs : m.transition q h with
      | ordinary a => simp [windowStep,replay,windowView,hs,Bool.and_assoc]
      | binary a d => cases b <;> simp [windowStep,replay,windowView,hs]

/-- The width-bounded witness predicate is a linear number of repeated local
kernel applications, consuming each certificate bit exactly once. -/
theorem finiteReplay_eq_fold (m : Machine) (x : Complexity.Bits) (clock : ℕ) (w : Fin clock → Bool) :
    finiteReplay m x clock w = finalBit m
      ((List.ofFn w).foldl (windowStep m) (encodeWindow m (x.length+clock) (initial m x),true)) := by
  rw [fold_windowStep]
  simp only [Bool.true_and]
  rfl

/-- Exact complete-path count using the finite local fold, with no additional
certificate bits beyond the original machine clock. -/
theorem count_eq_windowFold (M : PolynomialMachine) (x : Complexity.Bits) :
    M.count x = Fintype.card {w : Fin (M.time.eval x.length) → Bool //
      finalBit M.machine ((List.ofFn w).foldl (windowStep M.machine)
        (encodeWindow M.machine (x.length+M.time.eval x.length) (initial M.machine x),true))=true} := by
  rw [count_eq_finiteReplay]
  simp_rw [finiteReplay_eq_fold]

end PlanarHom.CountingCookLevin
