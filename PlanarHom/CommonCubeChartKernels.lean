-- RECOVERED exact bodies; import adapted to the proven conditional chart consequences.
import PlanarHom.AvailableConnectedBooleanTensor
noncomputable section
open Classical
namespace PlanarHom.ClosedMatrixFamily.CommonCubeChart
open LogarithmicSupport MatrixCoordinateTransport
variable {q : ℕ} {S : Set (Matrix (Fin q) (Fin q) ℝ)}
def kernel (W : CommonCubeChart S) (t : ℚ) : Matrix (Fin q) (Fin q) ℝ :=
  EntropyCompletion.distanceKernel (logSupport W.maximum) t
theorem kernel_mem (W : CommonCubeChart S) (hA : AlgebraicSourceClosed S)
    (htransfer : EffectiveSpectralClosed S) (t : ℚ) : W.kernel t ∈ S :=
  distanceKernel_mem S htransfer W.maximum W.admissible.mem W.admissible.posDef
    (hA.algebraic _ W.admissible.mem)
    (logSupport_connected W.admissible.posDef W.admissible.connected) W.positive_log t
theorem kernel_positive (W : CommonCubeChart S) (t : ℚ) (ht : 0<t) :
    ∀ i j,0<W.kernel t i j := by
  intro i j
  exact pow_pos (by exact_mod_cast ht) _
theorem reindex_kernel (W : CommonCubeChart S) (t : ℚ) :
    Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv (W.kernel t)=
      Boolean.tensor (fun _:Fin W.dimension=>(t:ℝ)) := by
  rw [kernel,reindex_distanceKernel W.graphIso]
  exact Boolean.cubeGraph_distanceKernel_eq_tensor _
end PlanarHom.ClosedMatrixFamily.CommonCubeChart
namespace PlanarHom.RectangularChartTransport
open scoped BigOperators
variable {X Y Z X' Y' Z' : Type} [Fintype Y] [Fintype Y']
theorem reindex_mul (eX : X≃X') (eY : Y≃Y') (eZ : Z≃Z')
    (A : Matrix X Y ℝ) (B : Matrix Y Z ℝ) :
    Matrix.reindex eX eZ (A*B)=Matrix.reindex eX eY A*Matrix.reindex eY eZ B :=
  (Matrix.reindexLinearEquiv_mul ℝ ℝ eX eY eZ A B).symm
omit [Fintype Y] [Fintype Y'] in
theorem reindex_transpose (eX : X≃X') (eY : Y≃Y') (A : Matrix X Y ℝ) :
    Matrix.reindex eY eX A.transpose=(Matrix.reindex eX eY A).transpose := rfl
theorem mul_positive [Nonempty Y] (A : Matrix X Y ℝ) (B : Matrix Y Z ℝ)
    (hA : ∀ i j,0<A i j) (hB : ∀ i j,0<B i j) : ∀ i j,0<(A*B) i j := by
  intro i j
  exact Finset.sum_pos (fun k _=>mul_pos (hA i k) (hB k j)) Finset.univ_nonempty
end PlanarHom.RectangularChartTransport
