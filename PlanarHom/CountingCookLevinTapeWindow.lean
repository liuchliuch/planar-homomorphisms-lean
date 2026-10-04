import PlanarHom.SingleTapeSharpPBridge
import PlanarHom.ParsimoniousBooleanProgram

/-!
# NEW reconstruction: finite-width faithful replay for counting Cook-Levin

The source is the actual single-tape machine already proved equivalent to the
independent #P class. Finite windows use one optional alphabet symbol per cell,
not an enumeration of all configurations. Canonical false bits at deterministic
and post-halt positions are retained from the established replay convention.
-/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic NondeterministicComputationTree

/-- Literal finite list representatives of the two sides of the real tape. -/
abbrev Raw (m : Machine) := (Control m.Q × m.Γ) × (List m.Γ × List m.Γ)

def erase (m : Machine) (c : Raw m) : m.Cfg := m.represented c.1.1 c.1.2 c.2.1 c.2.2

def initial (m : Machine) (x : Complexity.Bits) : Raw m :=
  ((.run m.start,(x.map m.input).head?.getD m.blank),([], (x.map m.input).tail))

@[simp] theorem erase_initial (m : Machine) (x : Complexity.Bits) :
    erase m (initial m x)=m.initial x := m.represented_initial x

def applyAction (m : Machine) (a : Action m.Γ m.Q) (c : Raw m) : Raw m :=
  let t := SingleTapeToNondeterministicTM2.moved m a c.2.1 c.2.2
  ((a.next,t.1),(t.2.1,t.2.2))

theorem erase_applyAction (m : Machine) (a : Action m.Γ m.Q) (c : Raw m) :
    erase m (applyAction m a c)=m.execute a (erase m c).2 :=
  SingleTapeToNondeterministicTM2.represented_moved m a c.1.2 c.2.1 c.2.2

def rawView (m : Machine) (c : Raw m) : NodeView (Raw m) :=
  match c.1.1 with
  | .accept => .accept
  | .reject => .reject
  | .run q => match m.transition q c.1.2 with
    | .ordinary a => .ordinary (applyAction m a c)
    | .binary a b => .binary (applyAction m a c) (applyAction m b c)

/-- The concrete list replay agrees with the actual mathlib-tape replay. -/
theorem replay_erase (m : Machine) (c : Raw m) (bs : List Bool) :
    replay (rawView m) c bs = replay m.view (erase m c) bs := by
  induction bs generalizing c with
  | nil =>
    rcases c with ⟨⟨q,head⟩,L,R⟩
    cases q with
    | accept => rfl
    | reject => rfl
    | run q => cases h : m.transition q head <;> simp [replay,rawView,erase,Machine.view,Machine.represented,h]
  | cons b bs ih =>
    rcases c with ⟨⟨q,head⟩,L,R⟩
    cases q with
    | accept => rfl
    | reject => rfl
    | run q =>
      cases h : m.transition q head with
      | ordinary a =>
        simp only [replay,rawView,erase,Machine.view,Machine.represented,h]
        rw [ih,erase_applyAction]
        rfl
      | binary a d =>
        cases b <;> simp only [replay,rawView,erase,Machine.view,Machine.represented,h,
          Bool.false_eq_true,↓reduceIte] <;> rw [ih,erase_applyAction] <;> rfl

/-- Every actual action grows each represented side by at most one cell. -/
theorem applyAction_length (m : Machine) (a : Action m.Γ m.Q) (c : Raw m) :
    (applyAction m a c).2.1.length ≤ c.2.1.length+1 ∧
      (applyAction m a c).2.2.length ≤ c.2.2.length+1 := by
  cases h : a.motion <;>
    simp [applyAction,SingleTapeToNondeterministicTM2.moved,h]
  <;> omega

/-- Window capacity is L+1, so the head cell of either side is always readable. -/
abbrev Window (m : Machine) (L : ℕ) :=
  (Control m.Q × m.Γ) × ((Fin (L+1) → Option m.Γ) × (Fin (L+1) → Option m.Γ))

def stackWindow {A : Type} (L : ℕ) (xs : List A) : Fin (L+1) → Option A := fun i => xs[i.val]?

def encodeWindow (m : Machine) (L : ℕ) (c : Raw m) : Window m L :=
  (c.1,(stackWindow L c.2.1,stackWindow L c.2.2))

def pushWindow {A : Type} {L : ℕ} (a : A) (v : Fin (L+1) → Option A) : Fin (L+1) → Option A :=
  Fin.cons (some a) (fun i => v i.castSucc)

def popWindow {A : Type} {L : ℕ} (v : Fin (L+1) → Option A) : Fin (L+1) → Option A :=
  Fin.lastCases none (fun i => v i.succ)

@[simp] theorem pushWindow_stackWindow {A : Type} (L : ℕ) (a : A) (xs : List A) :
    pushWindow a (stackWindow L xs)=stackWindow L (a::xs) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem popWindow_stackWindow {A : Type} (L : ℕ) (xs : List A) (hx : xs.length≤L+1) :
    popWindow (stackWindow L xs)=stackWindow L xs.tail := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [popWindow,Fin.lastCases_last,stackWindow,Fin.val_last,List.getElem?_tail]
    exact (List.getElem?_eq_none hx).symm
  · simp [popWindow,stackWindow]

/-- The finite window update accesses only the finite control, scanned symbol,
side heads and the immediately neighboring stored cell in each side vector. -/
def windowAction (m : Machine) {L : ℕ} (a : Action m.Γ m.Q) (c : Window m L) : Window m L :=
  match a.motion with
  | .stay => ((a.next,a.write),c.2)
  | .left => ((a.next,(c.2.1 0).getD m.blank),(popWindow c.2.1,pushWindow a.write c.2.2))
  | .right => ((a.next,(c.2.2 0).getD m.blank),(pushWindow a.write c.2.1,popWindow c.2.2))

/-- No overflow assumption is silently baked into the operation: its exact
precondition is the actual represented side-length bound. -/
theorem windowAction_encode (m : Machine) (L : ℕ) (a : Action m.Γ m.Q) (c : Raw m)
    (hL : c.2.1.length≤L+1) (hR : c.2.2.length≤L+1) :
    windowAction m a (encodeWindow m L c)=encodeWindow m L (applyAction m a c) := by
  cases h : a.motion <;>
    simp [windowAction,encodeWindow,applyAction,SingleTapeToNondeterministicTM2.moved,h,
      popWindow_stackWindow L c.2.1 hL,popWindow_stackWindow L c.2.2 hR,
      stackWindow,← List.head?_eq_getElem?]

/-- The same actual local instruction table, acting on fixed-width cell vectors. -/
def windowView (m : Machine) {L : ℕ} (c : Window m L) : NodeView (Window m L) :=
  match c.1.1 with
  | .accept => .accept
  | .reject => .reject
  | .run q => match m.transition q c.1.2 with
    | .ordinary a => .ordinary (windowAction m a c)
    | .binary a b => .binary (windowAction m a c) (windowAction m b c)

/-- Clock-plus-input capacity suffices for every branch, including branches
that repeatedly enter previously blank tape cells. -/
theorem replay_window (m : Machine) (L : ℕ) (c : Raw m) (bs : List Bool)
    (hL : c.2.1.length+bs.length≤L+1) (hR : c.2.2.length+bs.length≤L+1) :
    replay (windowView m) (encodeWindow m L c) bs = replay (rawView m) c bs := by
  induction bs generalizing c with
  | nil =>
    rcases c with ⟨⟨q,head⟩,ls,rs⟩
    cases q with
    | accept => rfl
    | reject => rfl
    | run q => cases h : m.transition q head <;> simp [replay,windowView,rawView,encodeWindow,h]
  | cons b bs ih =>
    have hnext (a : Action m.Γ m.Q) :
        replay (windowView m) (windowAction m a (encodeWindow m L c)) bs =
          replay (rawView m) (applyAction m a c) bs := by
      rw [windowAction_encode m L a c (by omega) (by omega)]
      have hb := applyAction_length m a c
      exact ih _ (by simp only [List.length_cons] at hL; omega)
        (by simp only [List.length_cons] at hR; omega)
    rcases c with ⟨⟨q,head⟩,ls,rs⟩
    cases q with
    | accept => rfl
    | reject => rfl
    | run q =>
      cases h : m.transition q head with
      | ordinary a =>
        simp only [replay,windowView,rawView,encodeWindow,h]
        exact congrArg (fun z => (!b)&&z) (hnext a)
      | binary a d =>
        cases b <;> simp only [replay,windowView,rawView,encodeWindow,h,
          Bool.false_eq_true,↓reduceIte]
        · exact hnext a
        · exact hnext d

/-- Actual finite-cell replay on an exactly clock-length certificate. -/
def finiteReplay (m : Machine) (x : Complexity.Bits) (clock : ℕ) (w : Fin clock → Bool) : Bool :=
  replay (windowView m) (encodeWindow m (x.length+clock) (initial m x)) (List.ofFn w)

theorem finiteReplay_eq (m : Machine) (x : Complexity.Bits) (clock : ℕ) (w : Fin clock → Bool) :
    finiteReplay m x clock w = replay m.view (m.initial x) (List.ofFn w) := by
  rw [finiteReplay,replay_window,replay_erase,erase_initial]
  · simp [initial]
    omega
  · simp [initial]
    omega

/-- No padding multiplicity: the finite-width Boolean witness predicate counts
exactly the actual accepting computations of the original single-tape machine. -/
theorem count_eq_finiteReplay (M : PolynomialMachine) (x : Complexity.Bits) :
    M.count x = Fintype.card {w : Fin (M.time.eval x.length) → Bool //
      finiteReplay M.machine x (M.time.eval x.length) w=true} := by
  simp_rw [finiteReplay_eq]
  exact acceptingCount_eq_card_replay M.machine.view _ _

/-- Every source #P function admits this actual fixed-machine, polynomial-width,
exact-length witness representation. This is a proved machine-model transfer. -/
theorem sharpP_finiteReplay {f : Complexity.Bits → ℕ} (hf : Complexity.SharpP f) :
    ∃ M : PolynomialMachine, ∀ x,
      f x = Fintype.card {w : Fin (M.time.eval x.length) → Bool //
        finiteReplay M.machine x (M.time.eval x.length) w=true} := by
  obtain ⟨M,hM⟩ := hf.singleTapeSharpP
  exact ⟨M,fun x => (hM x).trans (count_eq_finiteReplay M x)⟩

/-- Exact number of optional-symbol tape cells, before fixed alphabet one-hot
encoding; the alphabet/control cardinalities depend only on the source machine. -/
def windowCellPolynomial (clock : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2*(Polynomial.X+clock+Polynomial.C 1)

theorem windowCellPolynomial_eval (clock : Polynomial ℕ) (N : ℕ) :
    (windowCellPolynomial clock).eval N=2*(N+clock.eval N+1) := by
  simp [windowCellPolynomial]

end PlanarHom.CountingCookLevin
