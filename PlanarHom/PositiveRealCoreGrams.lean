import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Sqrt

/-! NEW literal square-root diagonal decoration used by the surviving moment
proofs. These definitions carry no algorithmic or classification assumption. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.PositiveRealCore
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def rootDiagonal (μ : I → ℝ) : Matrix I I ℝ := Matrix.diagonal (fun i=>Real.sqrt (μ i))

def decorated (B : Matrix I J ℝ) (μ : I → ℝ) (ν : J → ℝ) : Matrix I J ℝ :=
  rootDiagonal μ * B * rootDiagonal ν

theorem decorated_entry (B : Matrix I J ℝ) (μ : I → ℝ) (ν : J → ℝ) (i : I) (j : J) :
    decorated B μ ν i j = Real.sqrt (μ i) * B i j * Real.sqrt (ν j) := by
  simp [decorated,rootDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal]

end PlanarHom.PositiveRealCore
