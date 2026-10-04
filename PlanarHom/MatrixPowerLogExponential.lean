import PlanarHom.SpectralProductZeros
import PlanarHom.KernelContinuation

/-! The actual real-power family used by effective interpolation equals the
exponential of the scalar multiple of the genuine spectral logarithm. -/
noncomputable section
open scoped Matrix.Norms.Operator
namespace PlanarHom.SpectralProductZeros
variable {V : Type} [Fintype V] [DecidableEq V]

theorem realPower_eq_exp_smul_log (A : Matrix V V ℝ) (hA : A.PosDef) (t : ℝ) :
    realPower A t = NormedSpace.exp ℝ (t • EntropyCompletion.matrixLog A) := by
  have hlog : (EntropyCompletion.matrixLog A).IsHermitian := cfc_predicate Real.log A
  have hpos : ∀ x ∈ spectrum ℝ A, 0 < x := by
    intro x hx
    rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hA.eigenvalues_pos i
  have htlog : (t • EntropyCompletion.matrixLog A).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, star_trivial]
    rw [← hlog.apply i j]
    simp
  rw [← CFC.real_exp_eq_normedSpace_exp htlog.isSelfAdjoint]
  change cfc (fun x : ℝ => x ^ t) A = cfc Real.exp (t • cfc Real.log A)
  rw [← cfc_const_mul t Real.log A (A.finite_real_spectrum.continuousOn _)]
  rw [← cfc_comp' Real.exp (fun x : ℝ => t * Real.log x) A (by fun_prop)
    (A.finite_real_spectrum.continuousOn _) hA.1.isSelfAdjoint]
  apply cfc_congr
  intro x hx
  dsimp only
  rw [Real.rpow_def_of_pos (hpos x hx), mul_comm]

end PlanarHom.SpectralProductZeros
