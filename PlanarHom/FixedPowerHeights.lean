import PlanarHom.FixedAlphabetOutputBounds

/-! Actual canonical bit-length bounds for powers of fixed field values. -/

noncomputable section
namespace PlanarHom.FixedPowerHeights
open Complexity FixedAlphabetOutputBounds

/-- All prefixes of unary-counted exponentiation have a common polynomial bit bound. -/
theorem exists_polynomial_power_length_bound {K : Type} [Field K] [Algebra ℚ K]
    {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K) (A : K) :
    ∃ p : Polynomial ℕ, ∀ n i : ℕ, i ≤ n →
      ((numberFieldEncoding basis).encode (A ^ i)).length ≤ p.eval n := by
  obtain ⟨p, hp⟩ := exists_output_polynomial basis (fun _ : Unit => A) 1
  refine ⟨p, fun n i hi => ?_⟩
  have hw := hp (fun _ : Unit => List.replicate i ()) i (by intro j; simp) (by simp)
  have hb : ((numberFieldEncoding basis).encode (A ^ i)).length ≤ p.eval i := by
    simpa using hw
  exact hb.trans (MachineComposition.natPolynomial_monotone p hi)

end PlanarHom.FixedPowerHeights
