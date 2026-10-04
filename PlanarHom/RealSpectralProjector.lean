import PlanarHom.RealSpectralInterpolation

/-! The CFC target in spectral interpolation is the genuine orthogonal range
projector: it fixes the image of the PSD matrix, kills its kernel, and is a
Hermitian idempotent. These facts use the actual spectral theorem. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.RealSpectralInterpolation
variable {C : Type} [Fintype C] [DecidableEq C]

private theorem nonneg_of_mem (A : Matrix C C ℝ) (hA : A.PosSemidef)
    (x : ℝ) (hx : x ∈ spectrum ℝ A) : 0 ≤ x := by
  obtain ⟨i, rfl⟩ := scalar_surjective A x hx
  exact scalar_nonneg A hA i

/-- The range target is Hermitian, hence symmetric over the reals. -/
theorem rangeProjector_isHermitian (A : Matrix C C ℝ) : (rangeProjector A).IsHermitian :=
  cfc_predicate (fun x : ℝ => if 0 < x then 1 else 0) A

/-- Its scalar spectral values are zero or one, so it is idempotent. -/
theorem rangeProjector_idempotent (A : Matrix C C ℝ) :
    rangeProjector A * rangeProjector A = rangeProjector A := by
  change cfc (fun x : ℝ => if 0 < x then 1 else 0) A *
    cfc (fun x : ℝ => if 0 < x then 1 else 0) A = _
  rw [← cfc_mul _ _ _ (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> simp

/-- Multiplication by the source matrix already lands in its positive eigenspaces. -/
theorem rangeProjector_mul (A : Matrix C C ℝ) (hA : A.PosSemidef) :
    rangeProjector A * A = A := by
  calc
    rangeProjector A * A =
        cfc (fun x : ℝ => if 0 < x then 1 else 0) A * cfc (fun x : ℝ => x) A := by
      exact congrArg (fun B : Matrix C C ℝ => rangeProjector A * B)
        (cfc_id' ℝ A hA.1).symm
    _ = cfc (fun x : ℝ => (if 0 < x then 1 else 0) * x) A :=
      (cfc_mul _ _ _ (A.finite_real_spectrum.continuousOn _)
        (A.finite_real_spectrum.continuousOn _)).symm
    _ = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x hx
      by_cases hp : 0 < x
      · simp [hp]
      · have hz : x = 0 := le_antisymm (le_of_not_gt hp) (nonneg_of_mem A hA x hx)
        simp [hz]
    _ = A := cfc_id' ℝ A hA.1

/-- The projector factors through the source with its totalized spectral inverse. -/
theorem rangeProjector_factor (A : Matrix C C ℝ) (hA : A.PosSemidef) :
    rangeProjector A = cfc (fun x : ℝ => x⁻¹) A * A := by
  calc
    rangeProjector A = cfc (fun x : ℝ => x⁻¹ * x) A := by
      apply cfc_congr
      intro x hx
      by_cases hp : 0 < x
      · simp [hp, ne_of_gt hp]
      · have hz : x = 0 := le_antisymm (le_of_not_gt hp) (nonneg_of_mem A hA x hx)
        simp [hz]
    _ = cfc (fun x : ℝ => x⁻¹) A * cfc (fun x : ℝ => x) A :=
      cfc_mul _ _ _ (A.finite_real_spectrum.continuousOn _)
        (A.finite_real_spectrum.continuousOn _)
    _ = _ := congrArg (fun B : Matrix C C ℝ => cfc (fun x : ℝ => x⁻¹) A * B)
      (cfc_id' ℝ A hA.1)

/-- The exact action on every vector in the image of the source matrix. -/
theorem rangeProjector_on_image (A : Matrix C C ℝ) (hA : A.PosSemidef) (x : C → ℝ) :
    (rangeProjector A).mulVec (A.mulVec x) = A.mulVec x := by
  rw [Matrix.mulVec_mulVec, rangeProjector_mul A hA]

/-- The exact action on every vector in the kernel of the source matrix. -/
theorem rangeProjector_on_kernel (A : Matrix C C ℝ) (hA : A.PosSemidef)
    (x : C → ℝ) (hx : A.mulVec x = 0) : (rangeProjector A).mulVec x = 0 := by
  rw [rangeProjector_factor A hA, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- The range projector in the paper's orthogonal diagonalization formula. -/
theorem rangeProjector_diagonalization (A : Matrix C C ℝ) (hA : A.PosSemidef) :
    rangeProjector A = (hA.1.eigenvectorUnitary : Matrix C C ℝ) *
      Matrix.diagonal (fun i => if 0 < hA.1.eigenvalues i then 1 else 0) *
      star (hA.1.eigenvectorUnitary : Matrix C C ℝ) := by
  exact hA.1.cfc_eq (fun x : ℝ => if 0 < x then 1 else 0)

/-- The fixed rational power in the paper's same orthogonal eigenbasis. -/
theorem rationalPower_diagonalization (A : Matrix C C ℝ) (hA : A.PosDef) (r : ℚ) :
    rationalPower A r = (hA.1.eigenvectorUnitary : Matrix C C ℝ) *
      Matrix.diagonal (fun i => hA.1.eigenvalues i ^ (r : ℝ)) *
      star (hA.1.eigenvectorUnitary : Matrix C C ℝ) := by
  exact hA.1.cfc_eq (fun x : ℝ => x ^ (r : ℝ))

end PlanarHom.RealSpectralInterpolation
