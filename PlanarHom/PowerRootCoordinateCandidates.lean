import PlanarHom.PowerRootCoordinateMachines
import PlanarHom.MatrixRationalRootCandidateMachines

/-! # Actual constant-size coordinate candidates for number-field power roots

Every rational basis coordinate of any solution to `x^n=y` appears in its
respective candidate list. This includes all signs and all roots in the field.
The remaining recovery steps are tuple assembly, exact power testing and
selection of the prescribed real sign.
-/

noncomputable section
namespace PlanarHom.PowerRootCoordinateCandidates
open Complexity PowerRootCoordinateAnnihilator

variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K)

def candidates (n : ℕ) (i : Fin d) (y : K) : List ℚ :=
  MatrixRationalRootCandidates.candidates (traceMatrix basis n (dual basis i) y)

theorem coordinate_mem (n : ℕ) (hn : 0 < n) (i : Fin d) (x : K) :
    basis.equivFun x i ∈ candidates basis n i (x^n) :=
  MatrixRationalRootCandidates.root_mem_candidates _ _
    (coordinatePolynomial_root basis n hn i x)

theorem fp_candidates (n : ℕ) (i : Fin d) :
    FP (numberFieldEncoding basis) BitEncoding.rat.list (candidates basis n i) := by
  apply MatrixRationalRootCandidateMachines.fp_candidates
  intro j k
  exact PowerRootCoordinateMachines.fp_tensor_entry _ (rootMatrix basis n (dual basis i))
    (PowerRootCoordinateMachines.fp_rootMatrix_entry basis n (dual basis i)) _ j k

theorem candidates_length (n : ℕ) (i : Fin d) (y : K) :
    (candidates basis n i y).length ≤ 3^((n*d)^d)*(n*d)^d := by
  have h := MatrixRationalRootCandidates.candidates_length (traceMatrix basis n (dual basis i) y)
  have he := coordinatePolynomial_natDegree_eq basis n i y
  simp only [coordinatePolynomial, tracePolynomial, Matrix.charpoly_natDegree_eq_dim] at he
  simpa only [candidates, he] using h

end PlanarHom.PowerRootCoordinateCandidates
