import PlanarHom.SingleTapeNondeterministic
import Mathlib.Tactic.Ring

/-!
# A count-preserving literal single-tape to multistack compiler

Two stacks represent the tape strictly to the left and right of the scanned cell.
A finite register stores that cell. The transition syntax below consists solely
of TM2 push/pop/load/goto/halt instructions and a binary label choice. Input is
physically copied and reversed in a charged deterministic prefix.
-/
namespace PlanarHom.SingleTapeToNondeterministicTM2
open Turing Turing.TM2 Complexity NondeterministicComputationTree
open SingleTapeNondeterministic

inductive Stack where
  | input | output | left | right
  deriving DecidableEq, Fintype

def Alphabet (m : Machine) : Stack → Type
  | .input | .output => Bool
  | .left | .right => m.Γ

inductive Label (m : Machine) where
  | load | restore | start
  | ready (control : Control m.Q) (head : m.Γ)
  | apply (action : Action m.Γ m.Q)
  deriving Fintype

abbrev State (m : Machine) := m.Γ × Bool

def reset (m : Machine) (l : Label m) : Stmt (Alphabet m) (Label m) (State m) :=
  .load (fun _ => (m.blank, false)) (.goto (fun _ => l))

def program (m : Machine) : Label m → Stmt (Alphabet m) (Label m) (State m)
  | .load => .pop .input (fun _ b => (m.input (b.getD false), b.isSome))
      (.branch Prod.snd
        (.push .left Prod.fst (reset m .load)) (reset m .restore))
  | .restore => .pop .left (fun _ a => (a.getD m.blank, a.isSome))
      (.branch Prod.snd
        (.push .right Prod.fst (reset m .restore)) (reset m .start))
  | .start => .pop .right (fun _ a => (a.getD m.blank, false))
      (.goto (fun v => .ready (.run m.start) v.1))
  | .ready .accept _ => .push .output (fun _ => true) .halt
  | .ready .reject _ => .halt
  | .ready (.run q) a => match m.transition q a with
      | .ordinary action => .goto (fun _ => .apply action)
      | .binary _ _ => .halt
  | .apply a => match a.motion with
      | .stay => .load (fun _ => (a.write, false))
          (.goto (fun _ => .ready a.next a.write))
      | .left => .push .right (fun _ => a.write)
          (.pop .left (fun _ b => (b.getD m.blank, false))
            (.goto (fun v => .ready a.next v.1)))
      | .right => .push .left (fun _ => a.write)
          (.pop .right (fun _ b => (b.getD m.blank, false))
            (.goto (fun v => .ready a.next v.1)))

def branches (m : Machine) : Label m → Option (Label m × Label m)
  | .ready (.run q) a => match m.transition q a with
      | .ordinary _ => none
      | .binary a b => some (.apply a, .apply b)
  | _ => none

def finTM (m : Machine) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet m
  Λ := Label m
  main := .load
  σ := State m
  initialState := (m.blank, false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program m

def compile (m : Machine) : NondeterministicTM2.Machine where
  core := ⟨finTM m, Equiv.refl Bool, Equiv.refl Bool⟩
  finiteAlphabet := by intro k; cases k <;> dsimp [finTM, Alphabet] <;> infer_instance
  branch := branches m

def store (m : Machine) (xs out : Bits) (left right : List m.Γ) :
    ∀ k, List (Alphabet m k)
  | .input => xs
  | .output => out
  | .left => left
  | .right => right

def cfg (m : Machine) (l : Option (Label m)) (head : m.Γ)
    (xs out : Bits) (left right : List m.Γ) : (compile m).Cfg :=
  ⟨l, (head, false), store m xs out left right⟩

def ready (m : Machine) (q : Control m.Q) (head : m.Γ)
    (left right : List m.Γ) : (compile m).Cfg :=
  cfg m (some (.ready q head)) head [] [] left right

def applying (m : Machine) (a : Action m.Γ m.Q) (head : m.Γ)
    (left right : List m.Γ) : (compile m).Cfg :=
  cfg m (some (.apply a)) head [] [] left right

private theorem cfg_ext {m : Machine} {a b : (compile m).Cfg}
    (hl : a.l = b.l) (hv : a.var = b.var) (hs : a.stk = b.stk) : a = b := by
  cases a; cases b; cases hl; cases hv; cases hs; rfl

@[simp] theorem update_input (m : Machine) (xs ys out : Bits) (L R : List m.Γ) :
    Function.update (store m xs out L R) .input ys = store m ys out L R := by
  funext k; cases k <;> simp [store]

@[simp] theorem update_output (m : Machine) (xs out out' : Bits) (L R : List m.Γ) :
    Function.update (store m xs out L R) .output out' = store m xs out' L R := by
  funext k; cases k <;> simp [store]

@[simp] theorem update_left (m : Machine) (xs out : Bits) (L L' R : List m.Γ) :
    Function.update (store m xs out L R) .left L' = store m xs out L' R := by
  funext k; cases k <;> simp [store]

@[simp] theorem update_right (m : Machine) (xs out : Bits) (L R R' : List m.Γ) :
    Function.update (store m xs out L R) .right R' = store m xs out L R' := by
  funext k; cases k <;> simp [store]

/-- The concrete lists after one local write/move instruction. -/
def moved (m : Machine) (a : Action m.Γ m.Q) (L R : List m.Γ) :
    m.Γ × List m.Γ × List m.Γ :=
  match a.motion with
  | .stay => (a.write, L, R)
  | .left => (L.head?.getD m.blank, L.tail, a.write :: R)
  | .right => (R.head?.getD m.blank, a.write :: L, R.tail)

/-- The stack update implements the real mathlib tape operation, including a
move into the unvisited, infinitely blank part of the tape. -/
theorem represented_moved (m : Machine) (a : Action m.Γ m.Q) (head : m.Γ)
    (L R : List m.Γ) :
    m.represented a.next (moved m a L R).1 (moved m a L R).2.1
      (moved m a L R).2.2 = m.execute a (m.represented (.run m.start) head L R).2 := by
  rcases a with ⟨w, d, q⟩
  cases d <;> cases L <;> cases R <;> rfl

theorem apply_view (m : Machine) (a : Action m.Γ m.Q) (head : m.Γ)
    (L R : List m.Γ) :
    (compile m).view (applying m a head L R) =
      .ordinary (ready m a.next (moved m a L R).1 (moved m a L R).2.1
        (moved m a L R).2.2) := by
  cases h : a.motion <;>
    simp [NondeterministicTM2.Machine.view, applying, cfg, compile, branches,
      finTM, program, stepAux, h, ready, moved, store, Function.update]

theorem ordinary_view (m : Machine) (q : m.Q) (head : m.Γ)
    (L R : List m.Γ) (a : Action m.Γ m.Q) (h : m.transition q head = .ordinary a) :
    (compile m).view (ready m (.run q) head L R) =
      .ordinary (applying m a head L R) := by
  simp [NondeterministicTM2.Machine.view, ready, applying, cfg, compile, branches,
    finTM, program, stepAux, h]

theorem binary_view (m : Machine) (q : m.Q) (head : m.Γ)
    (L R : List m.Γ) (a b : Action m.Γ m.Q)
    (h : m.transition q head = .binary a b) :
    (compile m).view (ready m (.run q) head L R) =
      .binary (applying m a head L R) (applying m b head L R) := by
  simp [NondeterministicTM2.Machine.view, NondeterministicTM2.Machine.jump,
    ready, applying, cfg, compile, branches, h]

theorem accept_view (m : Machine) (head : m.Γ) (L R : List m.Γ) :
    (compile m).view (ready m .accept head L R) =
      .ordinary (cfg m none head [] [true] L R) := by
  simp [NondeterministicTM2.Machine.view, ready, cfg, compile, branches,
    finTM, program, stepAux, store]

theorem reject_view (m : Machine) (head : m.Γ) (L R : List m.Γ) :
    (compile m).view (ready m .reject head L R) =
      .ordinary (cfg m none head [] [] L R) := rfl

@[simp] theorem final_accept (m : Machine) (head : m.Γ) (L R : List m.Γ) :
    (compile m).view (cfg m none head [] [true] L R) = .accept := by
  simp [NondeterministicTM2.Machine.view, NondeterministicTM2.Machine.output,
    cfg, compile, finTM, store]
  rfl

@[simp] theorem final_reject (m : Machine) (head : m.Γ) (L R : List m.Γ) :
    (compile m).view (cfg m none head [] [] L R) = .reject := by
  simp [NondeterministicTM2.Machine.view, NondeterministicTM2.Machine.output,
    cfg, compile, finTM, store]

private theorem bounded_ordinary_next {C : Type} {v : C → NodeView C} {c d : C}
    {n : ℕ} (hv : v c = .ordinary d) (hb : Bounded v c (n+1)) : Bounded v d n := by
  cases hb <;> simp_all

private theorem bounded_binary_next {C : Type} {v : C → NodeView C} {c a b : C}
    {n : ℕ} (hv : v c = .binary a b) (hb : Bounded v c (n+1)) :
    Bounded v a n ∧ Bounded v b n := by
  cases hb <;> simp_all

private theorem count_ordinary {C : Type} {v : C → NodeView C} {c d : C}
    (hv : v c = .ordinary d) (n : ℕ) :
    acceptingCount v (n+1) c = acceptingCount v n d := by simp [acceptingCount, hv]

private theorem count_binary {C : Type} {v : C → NodeView C} {c a b : C}
    (hv : v c = .binary a b) (n : ℕ) :
    acceptingCount v (n+1) c = acceptingCount v n a + acceptingCount v n b := by
  simp [acceptingCount, hv]

/-- Every source transition takes exactly two target transitions. Source terminal
states take one further charged instruction to produce the halting output. -/
theorem simulation (m : Machine) (n : ℕ) (q : Control m.Q) (head : m.Γ)
    (L R : List m.Γ) (hb : Bounded m.view (m.represented q head L R) n) :
    Bounded (compile m).view (ready m q head L R) (2*n+1) ∧
      acceptingCount (compile m).view (2*n+1) (ready m q head L R) =
        acceptingCount m.view n (m.represented q head L R) := by
  induction n generalizing q head L R with
  | zero =>
      cases q with
      | accept =>
          exact ⟨.ordinary (accept_view m head L R) (.accept (final_accept m head L R)),
            by simp [acceptingCount, accept_view, Machine.view, Machine.represented]⟩
      | reject =>
          exact ⟨.ordinary (reject_view m head L R) (.reject (final_reject m head L R)),
            by simp [acceptingCount, reject_view, Machine.view, Machine.represented]⟩
      | run q =>
          cases h : m.transition q head <;> cases hb <;>
            simp_all [Machine.view, Machine.represented]
  | succ n ih =>
      cases q with
      | accept =>
          exact ⟨.ordinary (accept_view m head L R) (.accept (final_accept m head L R)),
            by simp [acceptingCount, accept_view, Machine.view, Machine.represented]⟩
      | reject =>
          exact ⟨.ordinary (reject_view m head L R) (.reject (final_reject m head L R)),
            by simp [acceptingCount, reject_view, Machine.view, Machine.represented]⟩
      | run q =>
          cases ht : m.transition q head with
          | ordinary a =>
              have hv : m.view (m.represented (.run q) head L R) =
                  .ordinary (m.execute a (m.represented (.run m.start) head L R).2) := by
                simp [Machine.view, Machine.represented, ht]
              have ha := bounded_ordinary_next hv hb
              rw [← represented_moved m a head L R] at ha
              obtain ⟨ba, ca⟩ := ih a.next (moved m a L R).1 (moved m a L R).2.1
                (moved m a L R).2.2 ha
              constructor
              · convert Bounded.ordinary (ordinary_view m q head L R a ht)
                  (Bounded.ordinary (apply_view m a head L R) ba) using 1
              · have he : 2 * (n+1) + 1 = (2*n+1)+1+1 := by omega
                rw [he, count_ordinary (ordinary_view m q head L R a ht),
                  count_ordinary (apply_view m a head L R), ca, count_ordinary hv, represented_moved]
          | binary a b =>
              have hv : m.view (m.represented (.run q) head L R) =
                  .binary (m.execute a (m.represented (.run m.start) head L R).2)
                    (m.execute b (m.represented (.run m.start) head L R).2) := by
                simp [Machine.view, Machine.represented, ht]
              obtain ⟨ha, hb⟩ := bounded_binary_next hv hb
              rw [← represented_moved m a head L R] at ha
              rw [← represented_moved m b head L R] at hb
              obtain ⟨ba, ca⟩ := ih a.next (moved m a L R).1 (moved m a L R).2.1
                (moved m a L R).2.2 ha
              obtain ⟨bb, cb⟩ := ih b.next (moved m b L R).1 (moved m b L R).2.1
                (moved m b L R).2.2 hb
              constructor
              · convert Bounded.binary (binary_view m q head L R a b ht)
                  (Bounded.ordinary (apply_view m a head L R) ba)
                  (Bounded.ordinary (apply_view m b head L R) bb) using 1
              · have he : 2 * (n+1) + 1 = (2*n+1)+1+1 := by omega
                rw [he, count_binary (binary_view m q head L R a b ht),
                  count_ordinary (apply_view m a head L R),
                  count_ordinary (apply_view m b head L R), ca, cb,
                  count_binary hv, represented_moved, represented_moved]


/-- A finite sequence consisting entirely of ordinary charged transitions. -/
inductive OrdinaryRun {C : Type} (v : C → NodeView C) : ℕ → C → C → Prop where
  | refl (c) : OrdinaryRun v 0 c c
  | cons {c d e n} (step : v c = .ordinary d) (tail : OrdinaryRun v n d e) :
      OrdinaryRun v (n+1) c e

namespace OrdinaryRun
variable {C : Type} {v : C → NodeView C}

theorem trans {a b c : C} {n k : ℕ} (h : OrdinaryRun v n a b)
    (h' : OrdinaryRun v k b c) : OrdinaryRun v (n+k) a c := by
  induction h with
  | refl => simpa using h'
  | cons hs ht ih => simpa [Nat.add_right_comm] using OrdinaryRun.cons hs (ih h')

theorem bounded {a b : C} {n fuel : ℕ} (h : OrdinaryRun v n a b)
    (hb : Bounded v b fuel) : Bounded v a (n+fuel) := by
  induction h with
  | refl => simpa using hb
  | cons hs ht ih => simpa [Nat.add_right_comm] using Bounded.ordinary hs (ih hb)

theorem count {a b : C} {n fuel : ℕ} (h : OrdinaryRun v n a b) :
    acceptingCount v (n+fuel) a = acceptingCount v fuel b := by
  induction h with
  | refl => simp
  | cons hs ht ih =>
      rw [Nat.add_right_comm, count_ordinary hs]
      exact ih
end OrdinaryRun

theorem load_cons_view (m : Machine) (b : Bool) (xs : Bits) (L R : List m.Γ) :
    (compile m).view (cfg m (some .load) m.blank (b::xs) [] L R) =
      .ordinary (cfg m (some .load) m.blank xs [] (m.input b :: L) R) := by
  simp [NondeterministicTM2.Machine.view, cfg, compile, branches, finTM, program,
    stepAux, store, reset, Function.update]

theorem load_nil_view (m : Machine) (L R : List m.Γ) :
    (compile m).view (cfg m (some .load) m.blank [] [] L R) =
      .ordinary (cfg m (some .restore) m.blank [] [] L R) := by
  simp [NondeterministicTM2.Machine.view, cfg, compile, branches, finTM, program,
    stepAux, store, reset, Function.update]

theorem restore_cons_view (m : Machine) (a : m.Γ) (L R : List m.Γ) :
    (compile m).view (cfg m (some .restore) m.blank [] [] (a::L) R) =
      .ordinary (cfg m (some .restore) m.blank [] [] L (a::R)) := by
  simp [NondeterministicTM2.Machine.view, cfg, compile, branches, finTM, program,
    stepAux, store, reset, Function.update]

theorem restore_nil_view (m : Machine) (R : List m.Γ) :
    (compile m).view (cfg m (some .restore) m.blank [] [] [] R) =
      .ordinary (cfg m (some .start) m.blank [] [] [] R) := by
  simp [NondeterministicTM2.Machine.view, cfg, compile, branches, finTM, program,
    stepAux, store, reset, Function.update]

theorem start_view (m : Machine) (R : List m.Γ) :
    (compile m).view (cfg m (some .start) m.blank [] [] [] R) =
      .ordinary (ready m (.run m.start) (R.head?.getD m.blank) [] R.tail) := by
  simp [NondeterministicTM2.Machine.view, cfg, ready, compile, branches, finTM,
    program, stepAux, store]

theorem load_run (m : Machine) (xs : Bits) (L R : List m.Γ) :
    OrdinaryRun (compile m).view (xs.length+1)
      (cfg m (some .load) m.blank xs [] L R)
      (cfg m (some .restore) m.blank [] [] ((xs.map m.input).reverse ++ L) R) := by
  induction xs generalizing L with
  | nil => simpa using OrdinaryRun.cons (load_nil_view m L R) (.refl _)
  | cons b xs ih =>
      simpa [List.reverse_cons, List.append_assoc] using
        OrdinaryRun.cons (load_cons_view m b xs L R) (ih (m.input b :: L))

theorem restore_run (m : Machine) (L R : List m.Γ) :
    OrdinaryRun (compile m).view (L.length+1)
      (cfg m (some .restore) m.blank [] [] L R)
      (cfg m (some .start) m.blank [] [] [] (L.reverse ++ R)) := by
  induction L generalizing R with
  | nil => simpa using OrdinaryRun.cons (restore_nil_view m R) (.refl _)
  | cons a L ih =>
      simpa [List.reverse_cons, List.append_assoc] using
        OrdinaryRun.cons (restore_cons_view m a L R) (ih (a::R))

theorem initial_eq (m : Machine) (x : Bits) :
    (compile m).initial x = cfg m (some .load) m.blank x [] [] [] := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [NondeterministicTM2.Machine.initial, compile, finTM,
      initList, cfg, store, Alphabet]

/-- The binary input is moved from the designated input stack to the actual two
stack tape representation. Both passes and the initial head pop are charged. -/
theorem input_run (m : Machine) (x : Bits) :
    OrdinaryRun (compile m).view (2*x.length+3) ((compile m).initial x)
      (ready m (.run m.start) ((x.map m.input).head?.getD m.blank)
        [] (x.map m.input).tail) := by
  rw [initial_eq]
  have hl := load_run m x [] []
  have hr := restore_run m (x.map m.input).reverse []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse,
    List.length_map] at hl hr
  have hs := OrdinaryRun.cons (start_view m (x.map m.input)) (.refl _)
  convert hl.trans (hr.trans hs) using 1
  omega

/-- Exact count preservation and all-branch halting, including the input loader. -/
theorem compile_correct (m : Machine) (x : Bits) (time : ℕ)
    (halts : Bounded m.view (m.initial x) time) :
    Bounded (compile m).view ((compile m).initial x) (2*time+2*x.length+4) ∧
      acceptingCount (compile m).view (2*time+2*x.length+4) ((compile m).initial x) =
        acceptingCount m.view time (m.initial x) := by
  have hs := simulation m time (.run m.start) ((x.map m.input).head?.getD m.blank)
    [] (x.map m.input).tail (by rw [Machine.represented_initial]; exact halts)
  rw [Machine.represented_initial] at hs
  constructor
  · convert (input_run m x).bounded hs.1 using 1
    omega
  · have hc := (input_run m x).count (fuel := 2*time+1)
    rw [hs.2] at hc
    have he : 2*x.length+3+(2*time+1) = 2*time+2*x.length+4 := by omega
    rw [he] at hc
    exact hc

/-- The polynomial-time target machine has a linear simulation overhead. -/
noncomputable def polynomialCompile (m : PolynomialMachine) : PolynomialNondeterministicMachine where
  machine := compile m.machine
  time := 2 * m.time + 2 * Polynomial.X + 4
  halts x := by
    convert (compile_correct m.machine x (m.time.eval x.length) (m.halts x)).1 using 1
    simp

theorem polynomialCompile_count (m : PolynomialMachine) (x : Bits) :
    (polynomialCompile m).count x = m.count x := by
  have hc := (compile_correct m.machine x (m.time.eval x.length) (m.halts x)).2
  simpa [PolynomialNondeterministicMachine.count, PolynomialMachine.count,
    polynomialCompile] using hc

/-- Every polynomially bounded conventional binary-choice single-tape accepting
count is in the independent finite-alphabet multistack counting class. -/
theorem singleTapeSharpP_implies_sharpP {f : Bits → ℕ}
    (h : SingleTapeSharpP f) : SharpP f := by
  obtain ⟨m, hm⟩ := h
  exact ⟨polynomialCompile m, fun x => (hm x).trans (polynomialCompile_count m x).symm⟩

end PlanarHom.SingleTapeToNondeterministicTM2

namespace PlanarHom.SingleTapeNondeterministic

/-- Conventional binary-choice single-tape polynomial counts belong to the
independent multistack class, via the literal count-preserving compiler. -/
theorem SingleTapeSharpP.sharpP {f : Complexity.Bits → ℕ}
    (h : SingleTapeSharpP f) : Complexity.SharpP f :=
  SingleTapeToNondeterministicTM2.singleTapeSharpP_implies_sharpP h

end PlanarHom.SingleTapeNondeterministic
