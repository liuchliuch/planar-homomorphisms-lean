import PlanarHom.NondeterministicTM2SpaceBounds
import PlanarHom.TM2SingleTapeCompiler
import Mathlib.Tactic.Ring

/-! # Polynomial clock for the local multistack-to-tape compiler

The clock is built from fixed syntax constants and the source polynomial. Input
conversion, halting checks, every rejecting branch, and every primitive tape edge
are included. The compiler correctness theorem supplies its instantiated bound.
-/
namespace PlanarHom.TM2SingleTapeClock
noncomputable section
open Turing NondeterministicTM2SpaceBounds TM2SingleTapeCompiler
open Polynomial

/-- A uniform primitive allowance for one source edge or terminal check.
`primitive` is the finite maximum/sum of the actual TM1 syntax costs. -/
def blockCost (m : Source) (primitive cap : ℕ) : ℕ :=
  primitive * (1 + operationConstant m * (2*(cap+pushConstant m)+3)) + 2

theorem blockCost_two_le (m : Source) (primitive cap : ℕ) : 2 ≤ blockCost m primitive cap := by
  dsimp [blockCost]; omega

theorem statement_cost_le (m : Source) (primitive cap size : ℕ) (l : m.core.tm.Λ)
    (hs : size ≤ cap) :
    primitive * (1 + TM2TapeStatementBounds.stackOps (m.core.tm.m l) *
      (2*(size+MachineComposition.pushBound (m.core.tm.m l))+3)) ≤ blockCost m primitive cap := by
  unfold blockCost
  have hp := push_le m l
  have ho := operations_le m l
  have hfactor : 2*(size+MachineComposition.pushBound (m.core.tm.m l))+3 ≤
      2*(cap+pushConstant m)+3 := by omega
  exact (Nat.mul_le_mul_left primitive (Nat.add_le_add_left
    (Nat.mul_le_mul ho hfactor) 1)).trans (Nat.le_add_right _ 2)

/-- Source stack growth gives a cap linear in input size and source time. -/
def spacePolynomial (m : Source) (p : Polynomial ℕ) : Polynomial ℕ :=
  X + C (pushConstant m) * p

/-- Each source edge and the final checker receive one full block allowance.
The input loader costs at most input length plus three real transitions. -/
def time (m : Source) (primitive : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  (X+C 3) + (p+C 1) *
    (C primitive * (C 1 + C (operationConstant m) *
      (C 2*(spacePolynomial m p+C (pushConstant m))+C 3)) + C 2)

@[simp] theorem spacePolynomial_eval (m : Source) (p : Polynomial ℕ) (n : ℕ) :
    (spacePolynomial m p).eval n = n+p.eval n*pushConstant m := by
  simp [spacePolynomial,Nat.mul_comm]

@[simp] theorem time_eval (m : Source) (primitive : ℕ) (p : Polynomial ℕ) (n : ℕ) :
    (time m primitive p).eval n = n+3+(p.eval n+1)*
      blockCost m primitive (n+p.eval n*pushConstant m) := by
  simp [time,blockCost]

end
end PlanarHom.TM2SingleTapeClock
