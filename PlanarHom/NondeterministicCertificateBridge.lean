import PlanarHom.NondeterministicSharpP
import PlanarHom.NondeterministicReplayCompiler

/-! # Compiling nondeterministic accepting computations to exact-length certificates

The replay compiler is a proved ordinary TM2 computer. A certificate contains
one bit per available transition; every deterministic step and every unused
post-halt position is forced to false. The independent computation-tree theorem
proves a bijection with complete accepting paths, including paths of different
lengths. No padding factor occurs in the count.
-/
namespace PlanarHom.Complexity
open NondeterministicComputationTree

namespace PolynomialNondeterministicMachine

/-- Exact agreement between machine-path count and the existing paired-input,
exactly-polynomial-length certificate convention. -/
theorem count_eq_certificateCount (M : PolynomialNondeterministicMachine) (x : Bits) :
    M.count x = certificateCount M.time (NondeterministicReplayCompiler.verifier M.machine) x := by
  exact acceptingCount_eq_card_replay M.machine.view (M.time.eval x.length) (M.machine.initial x)

/-- Every independent polynomial-time nondeterministic machine has a genuine
polynomial-time deterministic certificate verifier. -/
theorem certificateSharpP_count (M : PolynomialNondeterministicMachine) : CertificateSharpP M.count :=
  ⟨M.time,NondeterministicReplayCompiler.verifier M.machine,
    NondeterministicReplayCompiler.fp_verifier M.machine,M.count_eq_certificateCount⟩

end PolynomialNondeterministicMachine

theorem SharpP.certificateSharpP {f : Bits → ℕ} (h : SharpP f) : CertificateSharpP f := by
  obtain ⟨M,hM⟩ := h
  exact ⟨M.time,NondeterministicReplayCompiler.verifier M.machine,
    NondeterministicReplayCompiler.fp_verifier M.machine,
    fun x => (hM x).trans (M.count_eq_certificateCount x)⟩

/-- Certificate-class hardness already implies hardness for the independently
defined nondeterministic multistack machine class, by the actual replay compiler. -/
theorem CertificateSharpPHard.sharpPHard {oracle : Bits → Bits}
    (h : CertificateSharpPHard oracle) : SharpPHard oracle :=
  fun f hf => h f hf.certificateSharpP

end PlanarHom.Complexity
