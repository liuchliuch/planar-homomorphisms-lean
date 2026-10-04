import PlanarHom.FKTIsingMachines
import PlanarHom.FisherSignedCalibration
import PlanarHom.FisherInheritedRowCorrectness

/-! NEW adaptation of the recovered correctness consumer to the proved inherited
Fisher rotation compiler. All numerical targets and ordinary planar-input
promises are unchanged.

Numerical correctness of the actual ordinary-input Ising value program in
its original fixed field. No evaluator, embedding, orientation or matching
oracle is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.FKTIsingMachines
open Complexity MultiGraph MultiGraph.Kasteleyn
variable {K:Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension:ℕ}
variable (basis:Module.Basis (Fin dimension) ℚ K) (φ:K→+*ℝ)
variable {g:MixedCode} {bt ut:ℕ}

include basis in
theorem matchingValue_correct (hg:g.PlanarValid bt ut) (ρ:K):
    φ (matchingValue ρ g)=
      ((FisherCodePipeline.code g).toMultiGraph (FisherCodePipeline.valid hg.1)).perfectMatchingSum
        (fun e=>φ ((FisherCodePipeline.isingData ρ g).2.getD e.val 0)):=by
  exact FisherCubicCode.calibrated_evaluation basis φ
    (FisherCodePipeline.intermediate_valid hg.1) (FisherCodePipeline.intermediate_cubic hg.1)
    (orientation g)
    (FisherInheritedRowCode.orientationLog_isPfaffian hg)
    (FisherExpansionCode.weights g (FisherContourOrder.computedRows g)
      (FisherCodePipeline.isingWeights ρ g))

include basis in
theorem value_map_partition (hg:g.PlanarValid bt ut) (ρ:K) (hρ:1+φ ρ≠0):
    φ (value ρ g)=(g.toMultiGraph hg.1).partition (Boolean.W (φ ρ)) (fun _=>1):=by
  rw [value,map_mul,matchingValue_correct basis φ hg ρ]
  exact (FisherCodePipeline.ising_matching_identity φ hg.1 ρ hρ).symm

theorem map_partition (hg:g.Valid bt ut) (ρ:K):
    φ ((g.toMultiGraph hg).partition (matrix ρ) (fun _=>1))=
      (g.toMultiGraph hg).partition (Boolean.W (φ ρ)) (fun _=>1):=by
  simp only [MultiGraph.partition,map_sum,MultiGraph.assignmentWeight,map_mul,map_prod,
    matrix,Boolean.W,apply_ite,map_one]

include basis in
theorem value_eq_partition (hg:g.PlanarValid bt ut) (ρ:K) (hρ:1+φ ρ≠0):
    value ρ g=(g.toMultiGraph hg.1).partition (matrix ρ) (fun _=>1):=by
  apply φ.injective
  rw [value_map_partition basis φ hg ρ hρ,map_partition φ hg.1 ρ]

end PlanarHom.FKTIsingMachines
