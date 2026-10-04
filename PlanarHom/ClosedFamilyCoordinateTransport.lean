import PlanarHom.AlgebraicClosedMatrixFamily
import PlanarHom.CubeReindexTransport

/-! Coordinate transport for an actual source-closed family and its maximum.
The reindexed family is the literal image under one fixed color bijection. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Matrix.Norms.Operator
namespace PlanarHom.MatrixCoordinateTransport
open LogarithmicSupport
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem reindex_realPower (e : V ≃ W) (H : Matrix V V ℝ) (hH : H.PosDef) (t : ℝ) :
    Matrix.reindex e e (cfc (fun x : ℝ => x ^ t) H) =
      cfc (fun x : ℝ => x ^ t) (Matrix.reindex e e H) := by
  change Matrix.reindex e e (SpectralProductZeros.realPower H t) =
    SpectralProductZeros.realPower (Matrix.reindex e e H) t
  rw [SpectralProductZeros.realPower_eq_exp_smul_log H hH,
    SpectralProductZeros.realPower_eq_exp_smul_log _ (reindex_posDef e hH),
    reindex_exp, matrixLog_reindex e hH]
  rfl

def logSupport_reindex_iso (e : V ≃ W) (H : Matrix V V ℝ) (hH : H.PosDef) :
    logSupport H ≃g logSupport (Matrix.reindex e e H) where
  toEquiv := e
  map_rel_iff' := by
    intro i j
    change (e i ≠ e j ∧ EntropyCompletion.matrixLog (Matrix.reindex e e H) (e i) (e j) ≠ 0) ↔
      (i ≠ j ∧ EntropyCompletion.matrixLog H i j ≠ 0)
    rw [matrixLog_reindex e hH]
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem reindex_distanceKernel {G : SimpleGraph V} {G' : SimpleGraph W}
    (e : G ≃g G') (x : ℝ) :
    Matrix.reindex e.toEquiv e.toEquiv (EntropyCompletion.distanceKernel G x) =
      EntropyCompletion.distanceKernel G' x := by
  ext i j
  change x ^ G.dist (e.symm i) (e.symm j) = x ^ G'.dist i j
  congr 1
  unfold SimpleGraph.dist
  rw [Boolean.graphIso_edist_eq e]
  simp

end PlanarHom.MatrixCoordinateTransport

namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport MatrixCoordinateTransport
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def reindexedFamily (e : V ≃ W) (A : Set (Matrix V V ℝ)) : Set (Matrix W W ℝ) :=
  (Matrix.reindex e e) '' A

theorem mem_reindexedFamily (e : V ≃ W) (A : Set (Matrix V V ℝ))
    (H : Matrix V V ℝ) (hH : H ∈ A) :
    Matrix.reindex e e H ∈ reindexedFamily e A := ⟨H, hH, rfl⟩

theorem reindex_posDef_iff (e : V ≃ W) (H : Matrix V V ℝ) :
    (Matrix.reindex e e H).PosDef ↔ H.PosDef := by
  refine ⟨fun h => ?_, reindex_posDef e⟩
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using reindex_posDef e.symm h

theorem admissible_reindex_iff (e : V ≃ W) (A : Set (Matrix V V ℝ))
    (H : Matrix V V ℝ) :
    Admissible (reindexedFamily e A) (Matrix.reindex e e H) ↔ Admissible A H := by
  constructor
  · intro h
    obtain ⟨K, hK, heq⟩ := h.mem
    have hKH : K = H := (Matrix.reindexAlgEquiv ℝ ℝ e).injective heq
    subst K
    have hpd := (reindex_posDef_iff e H).mp h.posDef
    refine ⟨hK, ?_, hpd, ?_⟩
    · intro i j
      simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h.nonneg (e i) (e j)
    · exact (offDiagonalSupport_reindex_iso e H hpd.1).connected_iff.mpr h.connected
  · intro h
    exact ⟨mem_reindexedFamily e A H h.mem, fun i j => h.nonneg _ _,
      reindex_posDef e h.posDef,
      (offDiagonalSupport_reindex_iso e H h.posDef.1).connected_iff.mp h.connected⟩

theorem maximum_reindex (e : V ≃ W) (A : Set (Matrix V V ℝ))
    (M : Matrix V V ℝ) (hM : M.PosDef) (hmax : IsMaximum A M) :
    IsMaximum (reindexedFamily e A) (Matrix.reindex e e M) := by
  intro H hH
  obtain ⟨K, hK, rfl⟩ := hH.mem
  have hKad := (admissible_reindex_iff e A K).mp hH
  rw [← (logSupport_reindex_iso e K hKad.posDef).card_edgeFinset_eq,
    ← (logSupport_reindex_iso e M hM).card_edgeFinset_eq]
  exact hmax K hKad

theorem spectralParallelClosed_reindex (e : V ≃ W) (A : Set (Matrix V V ℝ))
    (hA : SpectralParallelClosed A) : SpectralParallelClosed (reindexedFamily e A) where
  rationalPower_mem := by
    intro H hH hpd r
    obtain ⟨K, hK, rfl⟩ := hH
    rw [← reindex_realPower e K ((reindex_posDef_iff e K).mp hpd)]
    exact mem_reindexedFamily e A _ (hA.rationalPower_mem K hK
      ((reindex_posDef_iff e K).mp hpd) r)
  entrywiseProduct_mem := by
    intro H hH K hK
    obtain ⟨H, hH, rfl⟩ := hH
    obtain ⟨K, hK, rfl⟩ := hK
    exact mem_reindexedFamily e A _ (hA.entrywiseProduct_mem H hH K hK)

end PlanarHom.ClosedMatrixFamily
