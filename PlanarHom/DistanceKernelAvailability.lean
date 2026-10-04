import PlanarHom.DistanceKernelProductIdentities
import PlanarHom.DistanceKernelEvaluationMachines
import PlanarHom.UniformMatrixPowerSimulation
import PlanarHom.UniformFixedFieldTransfer
import PlanarHom.PositiveExponentialEntries

/-! Actual joint availability of rational distance kernels, uniformly in the
rational parameter. This supplies the computational assertion in Lemma4.2;
maximal-support sparsity remains a separate statement. -/
noncomputable section
open scoped Matrix.Norms.Operator
namespace PlanarHom.DistanceKernelAvailability
open Complexity Complexity.MixedCode EffectiveProductTransfer FiniteLanguageAliases
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q bt ut dimension : ℕ}

def graph (A : Matrix (Fin q) (Fin q) K) : SimpleGraph (Fin q) :=
  LogarithmicSupport.offDiagonalSupport
    (EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix A))
    (cfc_predicate Real.log (SpectralFieldPresentation.realMatrix A))

omit [FiniteDimensional ℚ K] in
private theorem power_positive (A : Matrix (Fin q) (Fin q) K)
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef) (hG : (graph A).Connected)
    (hedge : ∀ i j, (graph A).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix A) i j)
    (n : ℕ) (hn : 1 ≤ n) (i j : Fin q) : 0 < matrixPowerRealFamily A n i j := by
  rw [matrixPowerRealFamily, SpectralProductZeros.realPower_eq_exp_smul_log _ hA]
  exact MatrixLogCoefficients.exp_positive_time_entry_pos _ (cfc_predicate Real.log _)
    hG hedge (n : ℝ) (by exact_mod_cast (Nat.zero_lt_of_lt hn)) i j

omit [FiniteDimensional ℚ K] in
private theorem identities (A : Matrix (Fin q) (Fin q) K)
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef) (hG : (graph A).Connected)
    (hedge : ∀ i j, (graph A).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix A) i j)
    (x : ℚ) : ProductIdentities (matrixPowerRealFamily A)
      (fun i j => (DistanceKernelEvaluationMachines.matrix (K := K) (graph A) x i j : ℝ)) := by
  simpa only [DistanceKernelEvaluationMachines.matrix_real] using
    DistanceKernelProductIdentities.productIdentities (SpectralFieldPresentation.realMatrix A) hA hG hedge (x : ℝ)

/-- Every fixed rational distance kernel is available with all original labels
retained. Its entries are returned in the original source field presentation. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (graph (M old)).Connected)
    (hedge : ∀ i j, (graph (M old)).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j)
    (x : ℚ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (DistanceKernelEvaluationMachines.matrix (graph (M old)) x)) U (fun _ => 1))
      (evaluationProblem basis M U (fun _ => 1)) :=
  spectral_reduction basis M U (M old) (DistanceKernelEvaluationMachines.matrix (graph (M old)) x)
    hA (DistanceKernelEvaluationMachines.matrix_symm _ _) 1 (by omega)
    (power_positive _ hA hG hedge) (identities _ hA hG hedge x)
    (evaluationProblem basis M U (fun _ => 1)) (UniformMatrixPowerSimulation.reduction basis M U old)

/-- Uniform source4.2 availability in bit(x), using the genuine rational codec.
Positive parameters are the source claim; the evaluator itself is total. -/
def uniformReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (graph (M old)).Connected)
    (hedge : ∀ i j, (graph (M old)).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j) :
    PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _ => 1)
        (DistanceKernelEvaluationMachines.matrix (graph (M old))) (fun x : ℚ => 0 < x))
      (evaluationProblem basis M U (fun _ => 1)) :=
  spectral_parameter_reduction basis BitEncoding.rat (fun x : ℚ => 0 < x) M U (M old)
    (DistanceKernelEvaluationMachines.matrix (graph (M old))) hA
    (fun x _ => DistanceKernelEvaluationMachines.matrix_symm _ x)
    (DistanceKernelEvaluationMachines.fp_matrix basis _) 1 (by omega)
    (power_positive _ hA hG hedge) (fun x _ => identities _ hA hG hedge x)
    (evaluationProblem basis M U (fun _ => 1)) (UniformMatrixPowerSimulation.reduction basis M U old)

/-- Composition retains the supplied original availability rather than choosing a new base oracle. -/
def jointlyAvailable (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (graph (M old)).Connected)
    (hedge : ∀ i j, (graph (M old)).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _ => 1)) base) :=
  (uniformReduction basis M U old hA hG hedge).trans available

end PlanarHom.DistanceKernelAvailability
