import PlanarHom.NondeterministicSharpP
import PlanarHom.NondeterministicRunCombinators
import Mathlib.Computability.Tape
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Conventional binary-choice single-tape nondeterministic machines

Configurations use mathlib's `Turing.Tape`, whose two half-tapes are quotients of
finite lists by trailing blank extension. A local transition reads one symbol,
writes one symbol, moves by at most one cell, and changes a finite control state.
The two binary alternatives are labelled and counted separately, even if equal.
-/
namespace PlanarHom.SingleTapeNondeterministic
open Turing NondeterministicComputationTree Complexity

inductive Control (Q : Type) where
  | run (state : Q)
  | accept
  | reject
  deriving DecidableEq, Fintype

inductive Motion where
  | stay | left | right
  deriving DecidableEq, Fintype

structure Action (Γ Q : Type) where
  write : Γ
  motion : Motion
  next : Control Q
  deriving Fintype

inductive Instruction (Γ Q : Type) where
  | ordinary (action : Action Γ Q)
  | binary (left right : Action Γ Q)

/-- A finite-state, finite-alphabet, binary-input single-tape machine. Acceptance
and rejection are explicit halting control states. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabetFinite : Fintype Γ]
  [controlFinite : Fintype Q]
  blank : Γ
  input : Bool → Γ
  input_injective : Function.Injective input
  input_ne_blank : ∀ b, input b ≠ blank
  start : Q
  transition : Q → Γ → Instruction Γ Q

attribute [instance] Machine.alphabetFinite Machine.controlFinite
instance (m : Machine) : Inhabited m.Γ := ⟨m.blank⟩

namespace Machine
abbrev Cfg (m : Machine) := Control m.Q × Tape m.Γ

def execute (m : Machine) (a : Action m.Γ m.Q) (t : Tape m.Γ) : m.Cfg :=
  (a.next, match a.motion with
    | .stay => t.write a.write
    | .left => (t.write a.write).move .left
    | .right => (t.write a.write).move .right)

def view (m : Machine) : m.Cfg → NodeView m.Cfg
  | (.accept, _) => .accept
  | (.reject, _) => .reject
  | (.run q, t) => match m.transition q t.head with
    | .ordinary a => .ordinary (m.execute a t)
    | .binary a b => .binary (m.execute a t) (m.execute b t)

def initial (m : Machine) (x : Bits) : m.Cfg :=
  (.run m.start, Tape.mk₁ (x.map m.input))

/-- The concrete representation used by the compiler maps directly into
mathlib's blank-extension quotient; finite trailing blanks have no significance. -/
def represented (m : Machine) (q : Control m.Q) (head : m.Γ)
    (left right : List m.Γ) : m.Cfg :=
  (q, ⟨head, ListBlank.mk left, ListBlank.mk right⟩)

@[simp] theorem represented_initial (m : Machine) (x : Bits) :
    m.represented (.run m.start) ((x.map m.input).head?.getD m.blank)
      [] (x.map m.input).tail = m.initial x := by
  cases x <;> rfl

end Machine

/-- Polynomial time bounds every branch of the actual tape computation tree. -/
structure PolynomialMachine where
  machine : Machine
  time : Polynomial ℕ
  halts : ∀ x : Bits, Bounded machine.view (machine.initial x) (time.eval x.length)

namespace PolynomialMachine

def count (m : PolynomialMachine) (x : Bits) : ℕ :=
  acceptingCount m.machine.view (m.time.eval x.length) (m.machine.initial x)

/-- This count includes all complete accepting computations, not certificates. -/
theorem count_eq_card_complete_paths (m : PolynomialMachine) (x : Bits) :
    letI := (m.halts x).completePathsFintype
    m.count x = Fintype.card (Σ n, AcceptingPath m.machine.view (m.machine.initial x) n) :=
  (m.halts x).acceptingCount_eq_card_completePaths

end PolynomialMachine

def SingleTapeSharpP (f : Bits → ℕ) : Prop :=
  ∃ m : PolynomialMachine, ∀ x, f x = m.count x

end PlanarHom.SingleTapeNondeterministic
