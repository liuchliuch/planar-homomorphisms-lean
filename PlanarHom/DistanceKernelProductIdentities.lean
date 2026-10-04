import PlanarHom.MatrixPowerLogExponential
import PlanarHom.MatrixExponentialRelations
import PlanarHom.EffectivePolynomialTransfer

/-! The exact upper-triangular product identities required by effective transfer
hold for distance kernels of connected positive logarithmic support. -/
noncomputable section
open scoped BigOperators Topology Matrix.Norms.Operator
namespace PlanarHom.DistanceKernelProductIdentities
open EffectiveProductTransfer SymmetricProductIdentities
variable {q : ℕ}

theorem productIdentities (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.PosDef)
    (hG : (LogarithmicSupport.offDiagonalSupport (EntropyCompletion.matrixLog A)
      (cfc_predicate Real.log A)).Connected)
    (hedge : ∀ i j, (LogarithmicSupport.offDiagonalSupport (EntropyCompletion.matrixLog A)
      (cfc_predicate Real.log A)).Adj i j → 0 < EntropyCompletion.matrixLog A i j)
    (x : ℝ) :
    ProductIdentities (SpectralProductZeros.realPower A)
      (EntropyCompletion.distanceKernel
        (LogarithmicSupport.offDiagonalSupport (EntropyCompletion.matrixLog A)
          (cfc_predicate Real.log A)) x) := by
  intro m _ a b _ _ he
  let e : (Σ u : Upper q, Fin (a u)) → Fin q × Fin q := fun k => k.1.val
  let f : (Σ u : Upper q, Fin (b u)) → Fin q × Fin q := fun k => k.1.val
  have hprod (t : ℝ) :
      (∏ k, NormedSpace.exp ℝ (t • EntropyCompletion.matrixLog A) (e k).1 (e k).2) =
        ∏ k, NormedSpace.exp ℝ (t • EntropyCompletion.matrixLog A) (f k).1 (f k).2 := by
    have h := congrFun he t
    simp only [SpectralProductZeros.realPower_eq_exp_smul_log A hA t] at h
    simpa only [e, f, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using h
  have h := MatrixLogCoefficients.distanceKernel_products_eq_of_exp_products_eq
    (EntropyCompletion.matrixLog A) (cfc_predicate Real.log A) hG hedge e f
    (Filter.Eventually.of_forall hprod) x
  simpa only [e, f, Fintype.prod_sigma, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h

end PlanarHom.DistanceKernelProductIdentities
