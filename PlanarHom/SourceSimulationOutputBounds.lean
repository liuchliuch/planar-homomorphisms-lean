import PlanarHom.OracleOutputAccounting

/-! Uniform answer-size bounds derived from actual bit-charged source simulations. -/
namespace PlanarHom.Complexity.PromisePolyTimeTuringReduction
open PlanarHom.MachineComposition

/-- A simulation's own work and communication bound pays for its final output. -/
noncomputable def outputPolynomial {target source : PromiseProblem}
    (r : PromisePolyTimeTuringReduction target source) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (machinePushBound r.machine.core.tm + 1) * r.time

theorem output_length_bound {target source : PromiseProblem}
    (r : PromisePolyTimeTuringReduction target source) (raw : Bits) (hraw : target.valid raw) :
    (target.value raw).length ≤ (outputPolynomial r).eval raw.length := by
  obtain ⟨steps, cost, qs, hr, hc, _⟩ := r.computes source.value (fun _ _ => rfl) raw hraw
  have hb := hr.output_length_bound
  have hm := Nat.mul_le_mul_left (machinePushBound r.machine.core.tm + 1) hc
  simp only [outputPolynomial, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C]
  omega

end PlanarHom.Complexity.PromisePolyTimeTuringReduction
