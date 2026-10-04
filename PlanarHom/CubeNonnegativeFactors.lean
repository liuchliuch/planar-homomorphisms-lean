import PlanarHom.CubeRationalKernelRigidity

/-!
# Nonnegative cube factors without connected support

The tensor conclusion in Proposition 4.8 applies to every nonnegative PD target,
including disconnected targets. Connectedness is needed only for strict entry
positivity, and algebraicity only for the algebraicity of the explicit ratios.
The hypotheses below remain numerical bounds on genuine rational candidates;
computational joint availability is a separate obligation.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.CubeTensorExponential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonnegativity of a full PD tensor suffices for nonnegative canonical factors. -/
theorem canonicalFactor_posDef_and_nonneg (N : Matrix (ι → Bool) (ι → Bool) ℝ)
    (hHerm : N.IsHermitian) (γ : ℝ) (F : ι → Matrix Bool Bool ℝ)
    (hN : N = γ • tensor F) (hγ : 0 < γ) (hF : ∀ r, (F r).PosDef)
    (hnonneg : ∀ z w, 0 ≤ N z w) (r : ι) :
    (canonicalFactor N r).PosDef ∧ ∀ a b, 0 ≤ canonicalFactor N r a b := by
  have hdiag : ∀ r, 0 < F r false false := fun r => posDef_diagonal_pos _ (hF r) false
  rw [← normalizedFactor_eq_canonical N hHerm γ F hN (ne_of_gt hγ)
    (fun r => ne_of_gt (hdiag r)) r]
  refine ⟨normalizedFactor_posDef F hF r, fun a b => ?_⟩
  exact mul_nonneg (inv_nonneg.mpr (hdiag r).le)
    (factor_entry_nonneg N γ F hN hγ hdiag hnonneg r a b)

end PlanarHom.CubeTensorExponential

namespace PlanarHom.CubeSandwichRigidity
open Boolean LogarithmicSupport SandwichMaximality CubeTensorExponential
variable {d : ℕ}

/-- All nonnegative PD targets have canonical nonnegative PD factors. The two
additional source conclusions are conditional only on their corresponding
additional target hypotheses, not built into the factorization assumptions. -/
theorem canonical_nonnegative_tensor_of_sandwich_maximality
    (C N : Matrix (Cube d) (Cube d) ℝ) (hC : C.IsHermitian) (hN : N.PosDef)
    (hCube : offDiagonalSupport C hC = cubeGraph d)
    (hedge : ∀ z w, (offDiagonalSupport C hC).Adj z w → 0 < C z w)
    (hsquare : RationalSquareSandwichEdgeBound C (EntropyCompletion.matrixLog N) hC IsSelfAdjoint.log)
    (hraw : RationalSandwichEdgeBound C (EntropyCompletion.matrixLog N) hC)
    (hschur : RationalSandwichSchurEdgeBound C (EntropyCompletion.matrixLog N) hC)
    (c b : ℝ) (hb : 0 < b)
    (hUniform : RationalSandwichEdgeBound (uniformDirectionMatrix d c b)
      (EntropyCompletion.matrixLog N) (uniformDirectionMatrix_isHermitian d c b))
    (hnonneg : ∀ z w, 0 ≤ N z w) :
    N = N zeroColor zeroColor • CubeTensorExponential.tensor (canonicalFactor N) ∧
      0 < N zeroColor zeroColor ∧
      (∀ r : Fin d, (canonicalFactor N r).PosDef ∧
        (∀ a b, 0 ≤ canonicalFactor N r a b) ∧ canonicalFactor N r false false = 1) ∧
      ((offDiagonalSupport N hN.1).Connected → ∀ r a b, 0 < canonicalFactor N r a b) ∧
      ((∀ z w, IsAlgebraic ℚ (N z w)) → ∀ r a b, IsAlgebraic ℚ (canonicalFactor N r a b)) := by
  let B := EntropyCompletion.matrixLog N
  let a := fun r : Fin d => B (unitBit r) (unitBit r) - B zeroColor zeroColor
  let w := fun r : Fin d => B zeroColor (unitBit r)
  let F := fun r : Fin d => NormedSpace.exp ℝ (localBlock (a r) (w r))
  let γ := Real.exp (B zeroColor zeroColor)
  have hfactor : N = γ • CubeTensorExponential.tensor F := by
    have h := exp_eq_tensor_of_sandwich_maximality C B hC IsSelfAdjoint.log
      hCube hedge hsquare hraw hschur c b hb hUniform
    rw [show NormedSpace.exp ℝ B = N from KernelContinuation.exp_matrixLog hN] at h
    exact h
  have hF : ∀ r, (F r).PosDef := fun r => exp_localBlock_posDef (a r) (w r)
  have hγ : 0 < γ := Real.exp_pos _
  have hdiag : ∀ r, F r false false ≠ 0 := fun r =>
    ne_of_gt (posDef_diagonal_pos _ (hF r) false)
  refine ⟨tensor_eq_canonical_factors N hN.1 γ F hfactor (ne_of_gt hγ) hdiag,
    posDef_diagonal_pos N hN zeroColor, ?_, ?_, ?_⟩
  · intro r
    obtain ⟨hpd, hnonneg⟩ := canonicalFactor_posDef_and_nonneg N hN.1 γ F hfactor hγ hF hnonneg r
    exact ⟨hpd, hnonneg, rfl⟩
  · intro hconn r
    exact (canonicalFactor_posDef_and_pos N hN.1 γ F hfactor hγ hF hnonneg hconn r).2
  · intro hAlg r a b
    exact canonicalFactor_isAlgebraic N hAlg r a b

/-- The full nonnegative-target conclusion with the positive uniform logarithm
selected from the actual rational cube distance-kernel construction. -/
theorem canonical_nonnegative_tensor_of_rational_kernel_maximality
    (C N : Matrix (Cube d) (Cube d) ℝ) (hC : C.IsHermitian) (hN : N.PosDef)
    (hCube : offDiagonalSupport C hC = cubeGraph d)
    (hedge : ∀ z w, (offDiagonalSupport C hC).Adj z w → 0 < C z w)
    (hsquare : RationalSquareSandwichEdgeBound C (EntropyCompletion.matrixLog N) hC IsSelfAdjoint.log)
    (hraw : RationalSandwichEdgeBound C (EntropyCompletion.matrixLog N) hC)
    (hschur : RationalSandwichSchurEdgeBound C (EntropyCompletion.matrixLog N) hC)
    (hKernel : ∀ q : ℚ, 0 < q → (q : ℝ) < 1 →
      RationalSandwichEdgeBound
        (EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel (cubeGraph d) q))
        (EntropyCompletion.matrixLog N) IsSelfAdjoint.log)
    (hnonneg : ∀ z w, 0 ≤ N z w) :
    N = N zeroColor zeroColor • CubeTensorExponential.tensor (canonicalFactor N) ∧
      0 < N zeroColor zeroColor ∧
      (∀ r : Fin d, (canonicalFactor N r).PosDef ∧
        (∀ a b, 0 ≤ canonicalFactor N r a b) ∧ canonicalFactor N r false false = 1) ∧
      ((offDiagonalSupport N hN.1).Connected → ∀ r a b, 0 < canonicalFactor N r a b) ∧
      ((∀ z w, IsAlgebraic ℚ (N z w)) → ∀ r a b, IsAlgebraic ℚ (canonicalFactor N r a b)) := by
  obtain ⟨q, hq, hq1, c, b, hb, heq⟩ :=
    UniformCubeKernelLog.exists_rat_uniform_positive_cube_log d
  have hUeq : EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel (cubeGraph d) q) =
      uniformDirectionMatrix d c b := heq
  have hUniform : RationalSandwichEdgeBound (uniformDirectionMatrix d c b)
      (EntropyCompletion.matrixLog N) (uniformDirectionMatrix_isHermitian d c b) := by
    have htransport : ∀ (A D : Matrix (Cube d) (Cube d) ℝ)
        (hA : A.IsHermitian) (hD : D.IsHermitian), A = D →
        RationalSandwichEdgeBound A (EntropyCompletion.matrixLog N) hA →
        RationalSandwichEdgeBound D (EntropyCompletion.matrixLog N) hD := by
      intro A D hA hD heq
      cases heq
      exact fun h => h
    exact htransport _ _ IsSelfAdjoint.log (uniformDirectionMatrix_isHermitian d c b)
      hUeq (hKernel q hq hq1)
  exact canonical_nonnegative_tensor_of_sandwich_maximality C N hC hN hCube hedge
    hsquare hraw hschur c b hb hUniform hnonneg

end PlanarHom.CubeSandwichRigidity
