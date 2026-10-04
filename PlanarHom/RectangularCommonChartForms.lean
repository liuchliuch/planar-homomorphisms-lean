import PlanarHom.CommonCubeChartKernels
import PlanarHom.RectangularPhysicalSourceForm
import PlanarHom.RectangularMixedPhysicalForms
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularChartTransport
open ClosedMatrixFamily RectangularMixedGadgets
variable {x y : ℕ}
theorem reindex_entrySquare {X Y X' Y' : Type} (eX : X≃X') (eY : Y≃Y')
    (B : Matrix X Y ℝ) :
    Matrix.reindex eX eY (entrySquare B)=entrySquare (Matrix.reindex eX eY B) := rfl
theorem reindex_three {X Y X' Y' : Type} [Fintype X] [Fintype Y]
    [Fintype X'] [Fintype Y'] (eX : X≃X') (eY : Y≃Y')
    (B : Matrix X Y ℝ) (K : Matrix Y Y ℝ) :
    Matrix.reindex eX eX (B*K*B.transpose)=
      Matrix.reindex eX eY B*Matrix.reindex eY eY K*(Matrix.reindex eX eY B).transpose := by
  rw [reindex_mul eX eY eX,reindex_mul eX eY eY,reindex_transpose]
theorem reindex_diamond {X Y X' Y' : Type} [Fintype X] [Fintype Y]
    [Fintype X'] [Fintype Y'] (eX : X≃X') (eY : Y≃Y')
    (B : Matrix X Y ℝ) (K : Matrix X X ℝ) :
    Matrix.reindex eX eX (entrySquare (K*B)*(entrySquare (K*B)).transpose)=
      entrySquare (Matrix.reindex eX eX K*Matrix.reindex eX eY B)*
      (entrySquare (Matrix.reindex eX eX K*Matrix.reindex eX eY B)).transpose := by
  rw [reindex_mul eX eY eX,reindex_transpose,reindex_entrySquare,reindex_mul eX eX eY]
theorem three_positive [Nonempty (Fin y)] (B : Matrix (Fin x) (Fin y) ℝ)
    (hB : ∀ i j,0<B i j) (K : Matrix (Fin y) (Fin y) ℝ) (hK : ∀ i j,0<K i j) :
    ∀ i j,0<(B*K*B.transpose) i j :=
  mul_positive _ _ (mul_positive _ _ hB hK) (fun i j=>hB j i)
theorem diamond_positive [Nonempty (Fin x)] [Nonempty (Fin y)]
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (K : Matrix (Fin x) (Fin x) ℝ) (hK : ∀ i j,0<K i j) :
    ∀ i j,0<(entrySquare (K*B)*(entrySquare (K*B)).transpose) i j := by
  have h := mul_positive K B hK hB
  exact mul_positive _ _ (fun i j=>pow_pos (h i j) 2) (fun i j=>pow_pos (h j i) 2)
end PlanarHom.RectangularChartTransport
