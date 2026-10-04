import PlanarHom.ClosedFamilySandwich
import PlanarHom.BooleanMatrix
import PlanarHom.ColoredSeriesGadget
import PlanarHom.ClosedFamilyCartesian

/-! The source-closed family tensor theorem in one fixed maximum cube chart.
Every numerical candidate bound is derived from rational powers, symmetric
series composition, parallel composition, and membership in the same family.
No support, opposite-edge, affine-diagonal or tensor identity is assumed.

This is the same-domain matrix-family assertion: the mixed outer-face gadgets
leave the two terminal colors free and sum only internal colors with unit
background. Thus prescribed terminal domains are retained when the theorem is
applied to their source-closed family. No definiteness premise on the original
source language occurs. Algebraicity is exactly the main-text family convention
encoded by `AlgebraicSourceClosed`; the explicit ratios inherit it from N. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix.Norms.Operator
namespace PlanarHom.ClosedMatrixFamily
open Boolean LogarithmicSupport MatrixCoordinateTransport CubeTensorExponential
open CubeSandwichRigidity
variable {q d : ℕ}

theorem tensor_in_fixed_coordinates_of_series
    (A : Set (Matrix (Fin q) (Fin q) ℝ)) (hA : AlgebraicSourceClosed A)
    (htransfer : EffectiveSpectralClosed A) (hseries : SymmetricSeriesClosed A)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j)
    (e : logSupport M ≃g cubeGraph d)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : N ∈ A) (hNpd : N.PosDef)
    (hnonneg : ∀ i j, 0 ≤ N i j) :
    (∀ i j, N i j = N (e.symm zeroColor) (e.symm zeroColor) *
      ∏ r : Fin d, factorInCoordinates e.toEquiv N r (e i r) (e j r)) ∧
    0 < N (e.symm zeroColor) (e.symm zeroColor) ∧
    IsAlgebraic ℚ (N (e.symm zeroColor) (e.symm zeroColor)) ∧
    (∀ r : Fin d, (factorInCoordinates e.toEquiv N r).PosDef ∧
      (∀ a b, 0 ≤ factorInCoordinates e.toEquiv N r a b) ∧
      (∀ a b, IsAlgebraic ℚ (factorInCoordinates e.toEquiv N r a b)) ∧
      factorInCoordinates e.toEquiv N r false false = 1) ∧
    ((offDiagonalSupport N hNpd.1).Connected ↔
      ∀ r a b, 0 < factorInCoordinates e.toEquiv N r a b) := by
  let A' := reindexedFamily e.toEquiv A
  let M' := Matrix.reindex e.toEquiv e.toEquiv M
  let N' := Matrix.reindex e.toEquiv e.toEquiv N
  have hM' : Admissible A' M' := (admissible_reindex_iff e.toEquiv A M).mpr hM
  have hmax' : IsMaximum A' M' := maximum_reindex e.toEquiv A M hM.posDef hmax
  have hA' : SpectralParallelClosed A' :=
    spectralParallelClosed_reindex e.toEquiv A hA.toSpectralParallelClosed
  have hseries' : SymmetricSeriesClosed A' := symmetricSeriesClosed_reindex e.toEquiv A hseries
  have hN' : N' ∈ A' := mem_reindexedFamily e.toEquiv A N hN
  have hNpd' : N'.PosDef := reindex_posDef e.toEquiv hNpd
  have hgraph : logSupport M' = cubeGraph d := by
    ext z w
    have he := e.map_adj_iff (v := e.symm z) (w := e.symm w)
    change (z ≠ w ∧ EntropyCompletion.matrixLog M' z w ≠ 0) ↔ _
    rw [show EntropyCompletion.matrixLog M' =
      Matrix.reindex e.toEquiv e.toEquiv (EntropyCompletion.matrixLog M) from
      matrixLog_reindex e.toEquiv hM.posDef]
    simpa [logSupport_adj, Matrix.reindex_apply, Matrix.submatrix_apply] using he.symm
  have hedge : ∀ z w, (logSupport M').Adj z w → 0 < EntropyCompletion.matrixLog M' z w := by
    intro z w hzw
    rw [show EntropyCompletion.matrixLog M' =
      Matrix.reindex e.toEquiv e.toEquiv (EntropyCompletion.matrixLog M) from
      matrixLog_reindex e.toEquiv hM.posDef]
    apply hpositive (e.symm z) (e.symm w)
    have he := e.map_adj_iff (v := e.symm z) (w := e.symm w)
    apply he.mp
    simpa using hgraph ▸ hzw
  obtain ⟨x, hx, hx1, c, b, hb, hUeq⟩ :=
    UniformCubeKernelLog.exists_rat_uniform_positive_cube_log d
  let H := EntropyCompletion.distanceKernel (cubeGraph d) (x : ℝ)
  have hH : H ∈ A' := by
    rw [show H = Matrix.reindex e.toEquiv e.toEquiv
      (EntropyCompletion.distanceKernel (logSupport M) (x : ℝ)) from
      (reindex_distanceKernel e (x : ℝ)).symm]
    exact mem_reindexedFamily e.toEquiv A _
      (distanceKernel_mem A htransfer M hM.mem hM.posDef (hA.algebraic M hM.mem)
        (logSupport_connected hM.posDef hM.connected) hpositive x)
  have hHpd : H.PosDef := by
    dsimp only [H]
    rw [cubeGraph_distanceKernel_eq_tensor]
    exact Boolean.tensor_posDef (fun _ => by exact_mod_cast hx) (fun _ => hx1)
  have hU : EntropyCompletion.matrixLog H = uniformDirectionMatrix d c b := hUeq
  have hHgraph : logSupport H = cubeGraph d := by
    ext z w
    change (z ≠ w ∧ EntropyCompletion.matrixLog H z w ≠ 0) ↔ _
    rw [hU]
    change (offDiagonalSupport (uniformDirectionMatrix d c b)
      (uniformDirectionMatrix_isHermitian d c b)).Adj z w ↔ _
    rw [uniformDirectionMatrix_support c b (ne_of_gt hb)]
  have hUniform : SandwichMaximality.RationalSandwichEdgeBound (uniformDirectionMatrix d c b)
      (EntropyCompletion.matrixLog N') (uniformDirectionMatrix_isHermitian d c b) := by
    have hu := rationalSandwichEdgeBound_of_same_card A' hA' hseries' M' H N' hM' hmax'
      hH hHpd hN' hNpd' (by rw [hHgraph, hgraph])
    simpa only [hU] using hu
  obtain ⟨heq, href, hfac, hpos, hAlg⟩ :=
    canonical_nonnegative_tensor_of_sandwich_maximality
      (EntropyCompletion.matrixLog M') N' IsSelfAdjoint.log hNpd' hgraph hedge
      (rationalSquareSandwichEdgeBound A' hA' hseries' M' N' hM' hmax' hN' hNpd')
      (rationalSandwichEdgeBound A' hA' hseries' M' N' hM' hmax' hN' hNpd')
      (rationalSandwichSchurEdgeBound A' hA' hseries' M' N' hM' hmax' hN' hNpd')
      c b hb hUniform (fun z w => hnonneg (e.symm z) (e.symm w))
  have hentry : ∀ i j, N i j = N (e.symm zeroColor) (e.symm zeroColor) *
      ∏ r : Fin d, factorInCoordinates e.toEquiv N r (e i r) (e j r) := by
    intro i j
    have h := congrFun (congrFun heq (e i)) (e j)
    change N (e.symm (e i)) (e.symm (e j)) =
      N (e.symm zeroColor) (e.symm zeroColor) *
        ∏ r : Fin d, factorInCoordinates e.toEquiv N r (e i r) (e j r) at h
    simpa using h
  refine ⟨hentry, href, hA.algebraic N hN _ _, ?_, ?_⟩
  · intro r
    exact ⟨(hfac r).1, (hfac r).2.1,
      hAlg (fun z w => hA.algebraic N hN (e.symm z) (e.symm w)) r, (hfac r).2.2⟩
  · constructor
    · intro hc
      exact hpos ((offDiagonalSupport_reindex_iso e.toEquiv N hNpd.1).connected_iff.mp hc)
    · intro hp
      letI : Nonempty (Fin q) := hM.connected.nonempty
      apply support_connected_of_positive_entries N hNpd.1
      intro i j
      rw [hentry i j]
      exact mul_pos href (Finset.prod_pos fun r _ => hp r _ _)

/-- **Proposition 4.8.** In the single fixed maximum cube chart, every
nonnegative PD member of the original source-closed family has the displayed
canonical algebraic nonnegative PD factors. Strict positivity is equivalent to
connected numerical support. The hypotheses are only the original closure
operations, actual membership and maximum, and the fixed cube isomorphism. -/
theorem proposition48
    (A : Set (Matrix (Fin q) (Fin q) ℝ)) (hA : AlgebraicSourceClosed A)
    (htransfer : EffectiveSpectralClosed A) (hgadget : MixedPlanarGadgetClosed A)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (hpositive : ∀ i j, (logSupport M).Adj i j → 0 < EntropyCompletion.matrixLog M i j)
    (e : logSupport M ≃g cubeGraph d)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : N ∈ A) (hNpd : N.PosDef)
    (hnonneg : ∀ i j, 0 ≤ N i j) :
    (∀ i j, N i j = N (e.symm zeroColor) (e.symm zeroColor) *
      ∏ r : Fin d, factorInCoordinates e.toEquiv N r (e i r) (e j r)) ∧
    0 < N (e.symm zeroColor) (e.symm zeroColor) ∧
    IsAlgebraic ℚ (N (e.symm zeroColor) (e.symm zeroColor)) ∧
    (∀ r : Fin d, (factorInCoordinates e.toEquiv N r).PosDef ∧
      (∀ a b, 0 ≤ factorInCoordinates e.toEquiv N r a b) ∧
      (∀ a b, IsAlgebraic ℚ (factorInCoordinates e.toEquiv N r a b)) ∧
      factorInCoordinates e.toEquiv N r false false = 1) ∧
    ((offDiagonalSupport N hNpd.1).Connected ↔
      ∀ r a b, 0 < factorInCoordinates e.toEquiv N r a b) :=
  tensor_in_fixed_coordinates_of_series A hA htransfer
    (fun H hH hsH K hK hsK => series_mem A hgadget H K hH hK hsH hsK)
    M hM hmax hpositive e N hN hNpd hnonneg

/-- Proposition 4.8 for an arbitrary supplied maximizing M. The positive-log
replacement has exactly its graph, and the supplied color equivalence itself
is retained, so every N uses precisely the original fixed coordinates. -/
theorem proposition48_fixed_maximum
    (A : Set (Matrix (Fin q) (Fin q) ℝ)) (hA : AlgebraicSourceClosed A)
    (htransfer : EffectiveSpectralClosed A) (hgadget : MixedPlanarGadgetClosed A)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : Admissible A M) (hmax : IsMaximum A M)
    (e : logSupport M ≃g cubeGraph d)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : N ∈ A) (hNpd : N.PosDef)
    (hnonneg : ∀ i j, 0 ≤ N i j) :
    (∀ i j, N i j = N (e.symm zeroColor) (e.symm zeroColor) *
      ∏ r : Fin d, factorInCoordinates e.toEquiv N r (e i r) (e j r)) ∧
    0 < N (e.symm zeroColor) (e.symm zeroColor) ∧
    IsAlgebraic ℚ (N (e.symm zeroColor) (e.symm zeroColor)) ∧
    (∀ r : Fin d, (factorInCoordinates e.toEquiv N r).PosDef ∧
      (∀ a b, 0 ≤ factorInCoordinates e.toEquiv N r a b) ∧
      (∀ a b, IsAlgebraic ℚ (factorInCoordinates e.toEquiv N r a b)) ∧
      factorInCoordinates e.toEquiv N r false false = 1) ∧
    ((offDiagonalSupport N hNpd.1).Connected ↔
      ∀ r a b, 0 < factorInCoordinates e.toEquiv N r a b) := by
  obtain ⟨P, hP, hPmax, heq, hpositive⟩ := exists_positive_same_graph A hA M hM hmax
  let e' : logSupport P ≃g cubeGraph d :=
    { toEquiv := e.toEquiv
      map_rel_iff' := by
        intro i j
        change (cubeGraph d).Adj (e i) (e j) ↔ (logSupport P).Adj i j
        rw [heq]
        exact e.map_adj_iff }
  exact proposition48 A hA htransfer hgadget P hP hPmax hpositive e' N hN hNpd hnonneg

end PlanarHom.ClosedMatrixFamily
