import PlanarHom.NondeterministicTM2

/-! # A counting class defined by nondeterministic finite-control machine runs

This is an independent finite-alphabet multistack TM2 definition: the polynomial
bounds every branch, and the value counts actual complete accepting paths.
`acceptingCount` is the equivalent finite recursion at the supplied clock. It
counts both choices at a binary node even if the successor configurations agree.
-/
namespace PlanarHom.Complexity
open NondeterministicTM2 NondeterministicComputationTree

/-- A binary-input, binary-choice, finite-alphabet multistack machine whose every
computation halts in polynomially many charged TM2 transitions. -/
structure PolynomialNondeterministicMachine where
  machine : Machine
  time : Polynomial ℕ
  halts : ∀ x : Bits, Bounded machine.view (machine.initial x) (time.eval x.length)

namespace PolynomialNondeterministicMachine

/-- Number of accepting computations, independently defined by the machine's
finite branching execution tree. -/
def count (M : PolynomialNondeterministicMachine) (x : Bits) : ℕ :=
  acceptingCount M.machine.view (M.time.eval x.length) (M.machine.initial x)

/-- Every independent complete accepting path is included in the clocked tree. -/
theorem path_length_le (M : PolynomialNondeterministicMachine) (x : Bits) {n : ℕ}
    (p : AcceptingPath M.machine.view (M.machine.initial x) n) : n ≤ M.time.eval x.length :=
  (M.halts x).path_length_le p

/-- The counted type contains all independent complete accepting computations,
with no certificate or padding data in it. -/
theorem count_eq_card_complete_paths (M : PolynomialNondeterministicMachine) (x : Bits) :
    letI := (M.halts x).completePathsFintype
    M.count x = Fintype.card (Σ n, AcceptingPath M.machine.view (M.machine.initial x) n) :=
  (M.halts x).acceptingCount_eq_card_completePaths

/-- Increasing the clock does not introduce extra accepting computations. -/
theorem count_eq_larger_clock (M : PolynomialNondeterministicMachine) (x : Bits)
    (n : ℕ) (hn : M.time.eval x.length ≤ n) :
    acceptingCount M.machine.view n (M.machine.initial x) = M.count x :=
  (M.halts x).acceptingCount_eq_of_le hn

end PolynomialNondeterministicMachine

/-- The nondeterministic finite-alphabet multistack #P class. No verifier occurs
in this definition. A tape-machine model-equivalence theorem is separate. -/
def SharpP (f : Bits → ℕ) : Prop :=
  ∃ M : PolynomialNondeterministicMachine, ∀ x, f x = M.count x

/-- Hardness quantifies over independent nondeterministic accepting-path counts. -/
def SharpPHard (oracle : Bits → Bits) : Prop :=
  ∀ f : Bits → ℕ, SharpP f → TuringReduces (fun x => BitEncoding.nat.encode (f x)) oracle

end PlanarHom.Complexity
