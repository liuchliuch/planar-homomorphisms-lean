import PlanarHom.CubeNonnegativeFactors

/-!
# Fixed arbitrary vertex coordinates for cube tensor rigidity

Matrix reindexing transports the genuine exponential, positive definiteness,
spectral logarithm and numerical support graph. This permits the same canonical
factors to be used in any fixed graph-isomorphism coordinates.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.MatrixCoordinateTransport
open LogarithmicSupport
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The actual exponential commutes with a simultaneous row and column reindex. -/
theorem reindex_exp (e : V ≃ W) (A : Matrix V V ℝ) :
    Matrix.reindex e e (NormedSpace.exp ℝ A) =
      NormedSpace.exp ℝ (Matrix.reindex e e A) := by
  exact NormedSpace.map_exp ℝ (Matrix.reindexAlgEquiv ℝ ℝ e)
    (Matrix.reindexAlgEquiv ℝ ℝ e).toLinearMap.continuous_of_finiteDimensional A

/-- Reindexing preserves positive definiteness, derived through the actual
Hermitian matrix logarithm and exponential. -/
theorem reindex_posDef (e : V ≃ W) {A : Matrix V V ℝ} (hA : A.PosDef) :
    (Matrix.reindex e e A).PosDef := by
  have hlog : (Matrix.reindex e e (EntropyCompletion.matrixLog A)).IsHermitian :=
    (show (EntropyCompletion.matrixLog A).IsHermitian from IsSelfAdjoint.log).submatrix e.symm
  have heq : Matrix.reindex e e A =
      NormedSpace.exp ℝ (Matrix.reindex e e (EntropyCompletion.matrixLog A)) := by
    rw [← reindex_exp, KernelContinuation.exp_matrixLog hA]
  rw [heq]
  exact ExponentialDual.exp_posDef hlog

/-- The genuine spectral logarithm commutes with reindexing of a PD matrix. -/
theorem matrixLog_reindex (e : V ≃ W) {A : Matrix V V ℝ} (hA : A.PosDef) :
    EntropyCompletion.matrixLog (Matrix.reindex e e A) =
      Matrix.reindex e e (EntropyCompletion.matrixLog A) := by
  have hlog : (Matrix.reindex e e (EntropyCompletion.matrixLog A)).IsHermitian :=
    (show (EntropyCompletion.matrixLog A).IsHermitian from IsSelfAdjoint.log).submatrix e.symm
  have heq : Matrix.reindex e e A =
      NormedSpace.exp ℝ (Matrix.reindex e e (EntropyCompletion.matrixLog A)) := by
    rw [← reindex_exp, KernelContinuation.exp_matrixLog hA]
  rw [heq, ExponentialDual.matrixLog_exp hlog]

/-- Reindexing identifies the actual numerical support graphs. -/
def offDiagonalSupport_reindex_iso (e : V ≃ W) (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    offDiagonalSupport A hA ≃g
      offDiagonalSupport (Matrix.reindex e e A) (hA.submatrix e.symm) where
  toEquiv := e
  map_rel_iff' := by
    intro v w
    simp [offDiagonalSupport_adj, Matrix.reindex_apply, Matrix.submatrix_apply]

end PlanarHom.MatrixCoordinateTransport

namespace PlanarHom.CubeTensorExponential
open Boolean
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The normalized local factor in a fixed arbitrary coordinate bijection. -/
def factorInCoordinates (e : V ≃ Cube d) (N : Matrix V V ℝ) (r : Fin d) :
    Matrix Bool Bool ℝ := canonicalFactor (Matrix.reindex e e N) r

/-- The factors use the original matrix's entries at the fixed reference vertex
and its single-bit neighbors. -/
theorem factorInCoordinates_entries (e : V ≃ Cube d) (N : Matrix V V ℝ) (r : Fin d) :
    factorInCoordinates e N r = fun a b =>
      if a then
        (if b then N (e.symm (unitBit r)) (e.symm (unitBit r)) /
          N (e.symm zeroColor) (e.symm zeroColor)
        else N (e.symm zeroColor) (e.symm (unitBit r)) /
          N (e.symm zeroColor) (e.symm zeroColor))
      else (if b then N (e.symm zeroColor) (e.symm (unitBit r)) /
          N (e.symm zeroColor) (e.symm zeroColor) else 1) := by
  ext a b
  simp only [factorInCoordinates, canonicalFactor,
    CubeSandwichRigidity.oneCoordinate_true_eq_unitBit, Matrix.reindex_apply,
    Matrix.submatrix_apply]

end PlanarHom.CubeTensorExponential

namespace PlanarHom.CubeSandwichRigidity
open Boolean LogarithmicSupport SandwichMaximality CubeTensorExponential MatrixCoordinateTransport
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The tensor classification in any fixed graph-isomorphism coordinates.
Every candidate bound concerns a literal reindex of the original matrices, and
the conclusion is an entry identity on the original vertex type. No target
connectedness or algebraicity assumption is needed for the base conclusion. -/
theorem canonical_tensor_in_fixed_graph_coordinates
    (C N : Matrix V V ℝ) (hC : C.IsHermitian) (hN : N.PosDef)
    (e : offDiagonalSupport C hC ≃g cubeGraph d)
    (hedge : ∀ i j, (offDiagonalSupport C hC).Adj i j → 0 < C i j)
    (hsquare : RationalSquareSandwichEdgeBound
      (Matrix.reindex e.toEquiv e.toEquiv C)
      (EntropyCompletion.matrixLog (Matrix.reindex e.toEquiv e.toEquiv N))
      (hC.submatrix e.symm) IsSelfAdjoint.log)
    (hraw : RationalSandwichEdgeBound
      (Matrix.reindex e.toEquiv e.toEquiv C)
      (EntropyCompletion.matrixLog (Matrix.reindex e.toEquiv e.toEquiv N))
      (hC.submatrix e.symm))
    (hschur : RationalSandwichSchurEdgeBound
      (Matrix.reindex e.toEquiv e.toEquiv C)
      (EntropyCompletion.matrixLog (Matrix.reindex e.toEquiv e.toEquiv N))
      (hC.submatrix e.symm))
    (hKernel : ∀ q : ℚ, 0 < q → (q : ℝ) < 1 →
      RationalSandwichEdgeBound
        (EntropyCompletion.matrixLog (EntropyCompletion.distanceKernel (cubeGraph d) q))
        (EntropyCompletion.matrixLog (Matrix.reindex e.toEquiv e.toEquiv N)) IsSelfAdjoint.log)
    (hnonneg : ∀ i j, 0 ≤ N i j) :
    (∀ i j, N i j = N (e.symm zeroColor) (e.symm zeroColor) *
      ∏ r : Fin d, factorInCoordinates e.toEquiv N r (e i r) (e j r)) ∧
    0 < N (e.symm zeroColor) (e.symm zeroColor) ∧
    (∀ r : Fin d, (factorInCoordinates e.toEquiv N r).PosDef ∧
      (∀ a b, 0 ≤ factorInCoordinates e.toEquiv N r a b) ∧
      factorInCoordinates e.toEquiv N r false false = 1) ∧
    ((offDiagonalSupport N hN.1).Connected →
      ∀ r a b, 0 < factorInCoordinates e.toEquiv N r a b) ∧
    ((∀ i j, IsAlgebraic ℚ (N i j)) →
      ∀ r a b, IsAlgebraic ℚ (factorInCoordinates e.toEquiv N r a b)) := by
  let C' := Matrix.reindex e.toEquiv e.toEquiv C
  let N' := Matrix.reindex e.toEquiv e.toEquiv N
  have hC' : C'.IsHermitian := hC.submatrix e.symm
  have hN' : N'.PosDef := reindex_posDef e.toEquiv hN
  have hCube : offDiagonalSupport C' hC' = cubeGraph d := by
    ext z w
    have h := e.map_adj_iff (v := e.symm z) (w := e.symm w)
    simpa [offDiagonalSupport_adj, C', Matrix.reindex_apply, Matrix.submatrix_apply] using h.symm
  have hedge' : ∀ z w, (offDiagonalSupport C' hC').Adj z w → 0 < C' z w := by
    intro z w h
    apply hedge (e.symm z) (e.symm w)
    exact ⟨fun hz => h.1 (e.symm.injective hz), h.2⟩
  obtain ⟨heq, href, hfac, hpos, hAlg⟩ :=
    canonical_nonnegative_tensor_of_rational_kernel_maximality C' N' hC' hN'
      hCube hedge' hsquare hraw hschur hKernel (fun z w => hnonneg (e.symm z) (e.symm w))
  refine ⟨?_, href, hfac, ?_, ?_⟩
  · intro i j
    have h := congrFun (congrFun heq (e i)) (e j)
    change N (e.symm (e i)) (e.symm (e j)) =
      N (e.symm zeroColor) (e.symm zeroColor) *
        ∏ r : Fin d, factorInCoordinates e.toEquiv N r (e i r) (e j r) at h
    have hi : e.symm (e i) = i := e.toEquiv.symm_apply_apply i
    have hj : e.symm (e j) = j := e.toEquiv.symm_apply_apply j
    rw [hi, hj] at h
    exact h
  · intro hconn
    apply hpos
    exact (offDiagonalSupport_reindex_iso e.toEquiv N hN.1).connected_iff.mp hconn
  · intro h
    exact hAlg (fun z w => h (e.symm z) (e.symm w))

end PlanarHom.CubeSandwichRigidity
