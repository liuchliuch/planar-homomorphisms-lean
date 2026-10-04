import PlanarHom.ParameterizedAppendSchurReduction
import PlanarHom.ParameterizedScalarReduction
import PlanarHom.EndpointLoopAvailability
import PlanarHom.DistanceKernelAvailability

/-! Actual uniform parameter availability for endpoint-decorated source matrices
Schur-multiplied by their logarithmic distance kernel. All original labels and
the original field presentation are retained. -/
set_option maxHeartbeats 800000
noncomputable section
namespace PlanarHom.EndpointLoopParameterAvailability
open Complexity Complexity.MixedCode FiniteLanguageAliases EndpointLoopMachines
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {dimension q b u : ℕ}

def family (A : Matrix (Fin q) (Fin q) K) (k : ℕ) (c : K) (x : ℚ) : Matrix (Fin q) (Fin q) K :=
  fun i j=>c*(decorated A k i j*DistanceKernelEvaluationMachines.matrix (DistanceKernelAvailability.graph A) x i j)

/-- The same exact family has a genuine fixed-field entry evaluator, uniform in
its rational parameter word; no spectral numerical routine is invoked. -/
theorem fp_family (basis : Module.Basis (Fin dimension) ℚ K)
    (A : Matrix (Fin q) (Fin q) K) (k : ℕ) (c : K) :
    FP BitEncoding.rat ((numberFieldEncoding basis).vector (q*q))
      (fun x=>binaryAlphabet (family A k c x)) := by
  apply FixedVectorMachines.fp_assemble
  intro e
  let i:=(finProdFinEquiv.symm e).1
  let j:=(finProdFinEquiv.symm e).2
  have hp:=(FixedFieldPolynomialMachines.fp_ratCast basis).comp
    (FixedFieldPolynomialMachines.fp_fixedPower basis ((DistanceKernelAvailability.graph A).dist i j))
  have h:=((fp_const BitEncoding.rat (numberFieldEncoding basis) (c*decorated A k i j)).pair hp).comp
    (FixedFieldArithmetic.fp_multiplication basis)
  exact h.congr (fun x=>by simp [family,binaryAlphabet,DistanceKernelEvaluationMachines.matrix,i,j,mul_assoc])

def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K) (old : Fin b) (k : ℕ) (c : K)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (DistanceKernelAvailability.graph (M old)).Connected)
    (hedge : ∀i j,(DistanceKernelAvailability.graph (M old)).Adj i j→
      0<EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _=>1)) base) :
    PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _=>1)
        (family (M old) k c) (fun x : ℚ=>0<x)) base := by
  let A:=decorated (M old) k
  let expanded:=appendOne M A
  let ER:=DistanceKernelEvaluationMachines.matrix (K:=K) (DistanceKernelAvailability.graph (M old))
  have he : expanded (Fin.castAdd 1 old)=M old:=appendOne_old M A old
  let kernel := DistanceKernelAvailability.uniformReduction basis expanded U (Fin.castAdd 1 old)
    (by simpa only [he] using hA) (by simpa only [he] using hG) (by simpa only [he] using hedge)
  have kernel' : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat expanded U (fun _=>1) ER (fun x : ℚ=>0<x))
      (evaluationProblem basis expanded U (fun _=>1)) := by
    simpa only [he] using kernel
  let simulation := kernel'.trans ((EndpointLoopMachines.reduction basis M U (fun _=>1) old k).trans available)
  let product := (ParameterizedAppendSchurReduction.reduction basis BitEncoding.rat M A U (fun _=>1)
    ER (fun x : ℚ=>0<x) base simulation).trans simulation
  change PromisePolyTimeTuringReduction
    (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _=>1)
      (fun x i j=>c*(A i j*ER x i j)) (fun x : ℚ=>0<x)) base
  exact (ParameterizedScalarReduction.reduction basis BitEncoding.rat M U (fun _=>1)
    (fun x i j=>A i j*ER x i j) (fun x : ℚ=>0<x) c base product).trans product

end PlanarHom.EndpointLoopParameterAvailability
