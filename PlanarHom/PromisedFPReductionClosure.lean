import PlanarHom.PromisePolynomialTime
import PlanarHom.OracleSubstitutionOnTrace
import PlanarHom.OracleReductionComposition

/-!
# NEW reconstruction: elimination of a promised FP oracle

This is a new replacement for the recovered 15-line historical wrapper of the
same module name, not a recovery of `RepresentedFPClosure` or its absent
`FixedRealPresentation.OracleModel` API. The public theorem retains exactly the
recovered type and the baseline's unchanged raw-bit promise encodings.

The implementation invokes the existing actual finite-control substitution
compiler on the reduction's legal query transcript. The callee is only required
to compute on the original source promise. There is no promise decider, new
representation, machine oracle, unit-cost arithmetic, or assumed output bound.
-/

noncomputable section
namespace PlanarHom.Complexity
open Turing PlanarHom.MachineComposition

namespace PromisedFPClosureReconstruction

/-- Every recorded answer is the actual oracle answer, by induction on the real
run derivation. This also covers repetitions and adaptive query transcripts. -/
theorem transcript_answer {m : OracleTM2} {oracle : Bits → Bits}
    {c d : m.Cfg} {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (hr : m.Run oracle c d steps cost qs) :
    ∀ q a, (q, a) ∈ qs → a = oracle q := by
  induction hr with
  | refl => simp
  | ordinary _ _ _ ih => exact ih
  | query _ _ _ ih =>
    intro q a hqa
    rcases List.mem_cons.mp hqa with hqa | hqa
    · cases hqa
      rfl
    · exact ih q a hqa

/-- Construct the ordinary TM2 computer by replacing every actual legal oracle
call with the promised solver. The resulting polynomial is the existing
cumulative compiler bound, including transfer, clearing and answer-bit costs. -/
def computer {P Q : PromiseProblem} (r : PromisePolyTimeTuringReduction P Q)
    (solver : TM2ComputableInPolyTime (BitEncoding.bits.restrict Q.valid).toFinEncoding
      BitEncoding.bits.toFinEncoding (fun x => Q.value x.val)) :
    TM2ComputableInPolyTime (BitEncoding.bits.restrict P.valid).toFinEncoding
      BitEncoding.bits.toFinEncoding (fun x => P.value x.val) := by
  let g := solver.toTM2ComputableAux
  refine {
    tm := OracleSubstitution.machine r.machine g
    inputAlphabet := r.machine.core.inputAlphabet
    outputAlphabet := r.machine.core.outputAlphabet
    time := OracleSubstitution.timePolynomial r.machine r.time solver.time
    outputsFun := ?_ }
  intro x
  apply Classical.choice
  obtain ⟨steps, cost, qs, hr, hcost, hgood⟩ :=
    r.computes Q.value (fun _ _ => rfl) x.val x.property
  have hN : ∀ k, ((r.machine.initial x.val).stk k).length ≤ x.val.length :=
    OracleReductionComposition.initial_length r.machine x.val
  obtain ⟨n, hn, he⟩ := OracleSubstitution.compiled_run_on_trace r.machine g hr
    solver.time (fun q a hqa => by
      have ha := transcript_answer hr q a hqa
      subst a
      exact solver.outputsFun ⟨q, hgood q (Q.value q) hqa⟩) x.val.length hN
  refine ⟨{ steps := n, evals_in_steps := ?_, steps_le_m := ?_ }⟩
  · rw [OracleSubstitution.idle_initial, OracleSubstitution.idle_final] at he
    exact he
  · exact hn.trans (OracleReductionComposition.bound_polynomial r.machine r.time
      solver.time x.val.length cost hcost)

end PromisedFPClosureReconstruction

/-- Exact promised FP closure, with the same public type as the recovered wrapper.
Both the reduction and solver are actual programs; all query validity and
charged running-time obligations are discharged by their existing witnesses. -/
theorem PromisePolyTimeTuringReduction.inFP {P Q : PromiseProblem}
    (r : PromisePolyTimeTuringReduction P Q) (hq : Q.InFP) : P.InFP :=
  ⟨PromisedFPClosureReconstruction.computer r hq.computer⟩

end PlanarHom.Complexity
