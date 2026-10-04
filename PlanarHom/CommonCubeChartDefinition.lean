import PlanarHom.ClosedFamilyTensor

/-! Exact surviving CommonCubeChart structure, extracted with a source-closed import. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ClosedMatrixFamily
open LogarithmicSupport Boolean CubeTensorExponential
variable {q : ℕ}
structure CommonCubeChart (S : Set (Matrix (Fin q) (Fin q) ℝ)) where
  dimension : ℕ
  maximum : Matrix (Fin q) (Fin q) ℝ
  admissible : Admissible S maximum
  isMaximum : IsMaximum S maximum
  positive_log : ∀ i j,(logSupport maximum).Adj i j→0<EntropyCompletion.matrixLog maximum i j
  graphIso : logSupport maximum ≃g cubeGraph dimension
end PlanarHom.ClosedMatrixFamily
