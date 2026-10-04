import PlanarHom.FixedFieldPolynomialMachines
import PlanarHom.SelectedProductClassSemantics
import PlanarHom.EntropyCompletion

/-! The rational-parameter distance kernel has an actual uniform fixed-field
entry evaluator, with every graph distance a fixed natural exponent. -/
noncomputable section
namespace PlanarHom.DistanceKernelEvaluationMachines
open Complexity Complexity.MixedCode
variable {K : Type} [Field K] [Algebra ℚ K] {dimension q : ℕ}

def matrix (G : SimpleGraph (Fin q)) (x : ℚ) : Matrix (Fin q) (Fin q) K :=
  fun i j => (algebraMap ℚ K x) ^ G.dist i j

theorem fp_matrix (basis : Module.Basis (Fin dimension) ℚ K) (G : SimpleGraph (Fin q)) :
    FP BitEncoding.rat ((numberFieldEncoding basis).vector (q*q))
      (fun x => binaryAlphabet (matrix (K := K) G x)) := by
  apply FixedVectorMachines.fp_assemble
  intro e
  exact (FixedFieldPolynomialMachines.fp_ratCast basis).comp
    (FixedFieldPolynomialMachines.fp_fixedPower basis
      (G.dist (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2))

theorem matrix_symm (G : SimpleGraph (Fin q)) (x : ℚ) (i j : Fin q) :
    matrix (K := K) G x i j = matrix G x j i := by simp [matrix, G.dist_comm]

@[simp] theorem matrix_diag (G : SimpleGraph (Fin q)) (x : ℚ) (i : Fin q) :
    matrix (K := K) G x i i = 1 := by simp [matrix, G.dist_self]

@[simp] theorem matrix_real {K : IntermediateField ℚ ℝ}
    (G : SimpleGraph (Fin q)) (x : ℚ) (i j : Fin q) :
    (matrix (K := K) G x i j : ℝ) = EntropyCompletion.distanceKernel G (x : ℝ) i j := by
  simp [matrix, EntropyCompletion.distanceKernel]

end PlanarHom.DistanceKernelEvaluationMachines
