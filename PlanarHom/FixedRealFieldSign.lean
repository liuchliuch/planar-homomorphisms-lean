import PlanarHom.FixedRealFieldSignMachines
import PlanarHom.AlgebraicRealApproximationMachines

/-! # Genuine polynomial-time sign in every fixed real number field

The algebraic basis constants have ordinary binary-precision approximation
machines. Fixed rational circuits evaluate these approximations at a precision
computed from exact inverse coordinates. The proved separation bound certifies
the resulting rational sign. No real comparison or approximation is an oracle.
-/
noncomputable section
namespace PlanarHom.FixedRealFieldSign
open Complexity
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K) (embedding : K →+* ℝ)

theorem embedding_isAlgebraic (x : K) : IsAlgebraic ℚ (embedding x) := by
  let f : K →ₐ[ℚ] ℝ := ⟨embedding, embedding.map_rat_algebraMap⟩
  exact IsAlgebraic.algHom f (IsAlgebraic.of_finite ℚ x)

/-- An unconditional ordinary polynomial-time machine for the fixed real embedding. -/
theorem fp_positive : FP (numberFieldEncoding basis) BitEncoding.bool
    (fun x => decide (0 < embedding x)) := by
  have h := fun i : Fin d => AlgebraicRealApproximationMachines.exists_fp_approximation
    (embedding (basis i)) (embedding_isAlgebraic embedding (basis i))
  choose f hfp hf using h
  exact fp_positive_of_approximations basis embedding f hfp hf

theorem fp_negative : FP (numberFieldEncoding basis) BitEncoding.bool
    (fun x => decide (embedding x < 0)) :=
  fp_negative_of_positive basis embedding (fp_positive basis embedding)

theorem fp_nonnegative : FP (numberFieldEncoding basis) BitEncoding.bool
    (fun x => decide (0 ≤ embedding x)) :=
  fp_nonnegative_of_positive basis embedding (fp_positive basis embedding)

theorem fp_less : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) BitEncoding.bool
    (fun p : K × K => decide (embedding p.1 < embedding p.2)) :=
  fp_less_of_positive basis embedding (fp_positive basis embedding)

theorem fp_sign : FP (numberFieldEncoding basis) BitEncoding.int (sign embedding) :=
  fp_sign_of_positive basis embedding (fp_positive basis embedding)

end PlanarHom.FixedRealFieldSign
