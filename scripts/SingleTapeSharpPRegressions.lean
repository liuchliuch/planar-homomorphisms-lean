import PlanarHom.SingleTapeSharpPHardness

namespace PlanarHom.SingleTapeSharpPRegressions
open Complexity NondeterministicComputationTree SingleTapeNondeterministic

/-- A conventional one-step machine with two distinct accepting choices,
even though they use identical write/move/next instructions. -/
def duplicateBranch : Machine where
  Γ := Option Bool
  Q := Unit
  blank := none
  input := some
  input_injective := fun _ _ h => Option.some.inj h
  input_ne_blank := by simp
  start := ()
  transition _ a := .binary ⟨a,.stay,.accept⟩ ⟨a,.stay,.accept⟩

theorem duplicateBranch_bounded (x : Bits) :
    Bounded duplicateBranch.view (duplicateBranch.initial x) 1 := by
  refine Bounded.binary (view := duplicateBranch.view) (n:=0) rfl ?_ ?_
  all_goals exact Bounded.accept rfl

noncomputable def duplicatePolynomialMachine : PolynomialMachine where
  machine := duplicateBranch
  time := Polynomial.C 1
  halts x := by simpa using duplicateBranch_bounded x

example (x : Bits) : duplicatePolynomialMachine.count x = 2 := by
  simp [PolynomialMachine.count,duplicatePolynomialMachine,acceptingCount,
    Machine.view,Machine.initial,Machine.execute,duplicateBranch]

example (x : Bits) :
    (SingleTapeToNondeterministicTM2.polynomialCompile duplicatePolynomialMachine).count x = 2 := by
  rw [SingleTapeToNondeterministicTM2.polynomialCompile_count]
  simp [PolynomialMachine.count,duplicatePolynomialMachine,acceptingCount,
    Machine.view,Machine.initial,Machine.execute,duplicateBranch]

example (x : Bits) :
    (SingleTapeToNondeterministicTM2.polynomialCompile duplicatePolynomialMachine).time.eval x.length =
      2*x.length+6 := by
  simp [SingleTapeToNondeterministicTM2.polynomialCompile,duplicatePolynomialMachine]
  omega

example (f : Bits → ℕ) (h : SingleTapeSharpP f) : SharpP f := h.sharpP
example (f : Bits → ℕ) (h : SingleTapeSharpP f) : CertificateSharpP f := h.certificateSharpP
example (oracle : Bits → Bits) (h : CertificateSharpPHard oracle) : SingleTapeSharpPHard oracle :=
  h.singleTapeSharpPHard

#check SingleTapeToNondeterministicTM2.represented_moved
#check SingleTapeToNondeterministicTM2.compile_correct
#check SingleTapeToNondeterministicTM2.polynomialCompile_count
#check SingleTapeSharpP.sharpP
#check CertificateSharpPHard.singleTapeSharpPHard
#print axioms SingleTapeToNondeterministicTM2.compile_correct
#print axioms SingleTapeSharpP.sharpP
#print axioms CertificateSharpPHard.singleTapeSharpPHard

end PlanarHom.SingleTapeSharpPRegressions
