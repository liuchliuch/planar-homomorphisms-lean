import PlanarHom.DynamicParameterizedGraphReduction
import PlanarHom.ParameterizedPowerReduction
import PlanarHom.DistanceKernelAvailability

/-! NEW actual uniform two-edge squared distance-kernel simulation. The raw
unary parameter and all original companion labels/unaries are retained. -/
noncomputable section
namespace PlanarHom.UniformSquaredDistanceKernel
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines
open ArithmeticCircuitPrimitives
variable {K : Type} [Field K] [Algebra ℚ K] {dimension q bt ut : ℕ}

def prepare (bt : ℕ) (p : ℕ×MixedCode) : Bits×List (ℚ×MixedCode) :=
  ([],[((p.1:ℚ),p.2.stretchLabel bt bt 1)])

theorem fp_prepare (bt : ℕ) : FP DynamicMatrixFamilySource.queryEncoding
    (BitEncoding.bits.prod (BitEncoding.rat.prod encoding).list) (prepare bt) := by
  let input:=DynamicMatrixFamilySource.queryEncoding
  have hn:=fp_fst BitEncoding.unaryNat encoding
  have hrat : FP input BitEncoding.rat (fun p=> (p.1:ℚ)) :=
    (((hn.comp UnaryNatConversionMachine.fp_conversion).comp fp_nat_int).comp fp_int_rat).congr
      (fun _=>by simp)
  have hg:=fp_snd BitEncoding.unaryNat encoding
  have hs:=((fp_const input BitEncoding.unaryNat 1).pair hg).comp (fp_stretchLabel bt bt)
  have hq:=hrat.pair hs
  have hlist:=(hq.pair (fp_const input (BitEncoding.rat.prod encoding).list [])).comp
    (ListMutationMachines.fp_cons (BitEncoding.rat.prod encoding))
  exact (fp_const input BitEncoding.bits []).pair hlist

def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K)
    (F : ℚ→Matrix (Fin q) (Fin q) K) (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _=>1) F
        (fun t=>0<t)) base) :
    PromisePolyTimeTuringReduction
      (DynamicMatrixFamilySource.problem basis M U (fun _=>1) (fun n=>F (n:ℚ)^2))
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _=>1) F
        (fun t=>0<t)) := by
  apply DynamicParameterizedGraphReduction.reductionOfPipeline basis BitEncoding.rat BitEncoding.bits
    M U M U (fun n=>F (n:ℚ)^2) F (fun t=>0<t)
    (prepare bt) ParameterizedPowerReduction.recover (fp_prepare bt)
    (ParameterizedPowerReduction.fp_recover basis) ?_ ?_ base available
  · intro p hn hg query hq
    obtain rfl:=List.mem_singleton.mp hq
    refine ⟨?_,ParameterizedPowerReduction.query_planar p.2 hg 1⟩
    change (0:ℚ)<p.1
    exact_mod_cast (show 0<p.1 by omega)
  · intro p hn hg
    have hv:=ParameterizedPowerReduction.query_valid p.2 hg.1 1
    simp only [prepare,ParameterizedPowerReduction.recover,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,ParameterizedMatrixEvaluation.answer,
      DynamicMatrixFamilySource.answer,totalEvaluation_valid _ _ _ _ hg.1,
      totalEvaluation_valid _ _ _ _ hv]
    exact ParameterizedPowerReduction.evaluate_query p.2 hg.1 1 M (F (p.1:ℚ)) U

def available (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin q) (Fin q) K) (U : Fin ut→Fin q→K)
    (F : ℚ→Matrix (Fin q) (Fin q) K) (base : PromiseProblem)
    (source : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis BitEncoding.rat M U (fun _=>1) F
        (fun t=>0<t)) base) :
    PromisePolyTimeTuringReduction
      (DynamicMatrixFamilySource.problem basis M U (fun _=>1) (fun n=>F (n:ℚ)^2)) base :=
  (reduction basis M U F base source).trans source

end PlanarHom.UniformSquaredDistanceKernel

namespace PlanarHom.DistanceKernelAvailability
open Complexity Complexity.MixedCode
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {q bt ut dimension : ℕ}

/-- The actual source 3.10(ii) simulator for the squared distance kernels.
No additional availability, graph-normalization or runtime premise is supplied. -/
def uniformSquareReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (graph (M old)).Connected)
    (hedge : ∀ i j, (graph (M old)).Adj i j →
      0 < EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j) :
    PromisePolyTimeTuringReduction
      (DynamicMatrixFamilySource.problem basis M U (fun _=>1)
        (fun n => DistanceKernelEvaluationMachines.matrix (graph (M old)) (n:ℚ) ^ 2))
      (evaluationProblem basis M U (fun _=>1)) :=
  UniformSquaredDistanceKernel.available basis M U
    (DistanceKernelEvaluationMachines.matrix (graph (M old))) _
    (uniformReduction basis M U old hA hG hedge)

end PlanarHom.DistanceKernelAvailability
